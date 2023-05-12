'''
--------Asim's Simple Smart Solutions----------------

Python Program for namaz timings alert

Version 1.0 - 11.11.2021

Coded By: Asim Abbas(asim1911@hotmail.com)
          Electrical Engineer
          
Hardware Included:
1. Raspberry Pi 3
2. HDMI display
3. AUX cable to play azan sound


**************************************************************************

CONFIDENTIAL
_________

The application is provided for the purpose of calculating namaz (prayer times)
for the Masjid in Sudenburg, Magdeburg, Germany

**************************************************************************

'''

raspberryOS = False  # Setting to true if raspberry pi OS otherwise false

# Setting the kivy environment variable
# (https://kivy.org/doc/stable/guide/environment.html)

if raspberryOS:
    import os

    os.environ["KIVY_GL_BACKEND"] = "gl"
    os.environ["KIVY_WINDOW"] = "egl_rpi"
    os.environ["KIVY_BCM_DISPMANX_ID"] = "2"

## Kivy configuration
from kivy.config import Config

Config.set('graphics', 'width', '1280')
Config.set('graphics', 'height', '1024')
Config.set('kivy', 'exit_on_escape', '1')

## Importing kivy libraries
from kivy.app import App
from kivy.lang import Builder
from kivy.uix.popup import Popup
from kivy.uix.label import Label
from kivy.uix.button import Button
from kivy.uix.image import Image
from kivy.core.window import Window
from kivy.uix.scatter import Scatter
from kivy.uix.textinput import TextInput
from kivy.clock import Clock, ClockEvent
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.gridlayout import GridLayout
from kivy.uix.floatlayout import FloatLayout
from kivy.graphics.context_instructions import Color
from kivy.graphics.vertex_instructions import Rectangle
from kivy.properties import ListProperty, ObjectProperty, NumericProperty

import re  # for splitting of strings
import datetime  # for calculating date and time
import math  # for ceil and floor
import time as tm  # for calculating time span
import calendar  # for getting the date of last sundays
import bidi.algorithm  # for arabic text "pip3 install python-bidi"
import arabic_reshaper  # for arabic text "pip3 install arabic-reshaper"
from hijri_converter import Hijri, Gregorian  # for Hijri date "pip3 install hijri-converter"
from datetime import date, timedelta, datetime, time
from numpy_ringbuffer import RingBuffer

import numpy as np
import prayerTimes as pT
import pygame

# Writing the log file with date and time in file name
_write2file = True  # Flag to check if write to file or not
if raspberryOS:
    _arialFont = '/home/pi/namazTimes/fonts/arial.ttf'
    _fileName = '/home/pi/namazTimes/log' + str(date.today()) + '.txt'
    _adhanAudio = '/home/pi/namazTimes/hayyaAllalSalah.mp3'

    _imgSourceFajr = '/home/pi/namazTimes/fajrNotify.png'
    _imgSourceDhuhr = '/home/pi/namazTimes/dhuhrNotify.png'
    _imgSourceAsr = '/home/pi/namazTimes/asrNotify.png'
    _imgSourceMaghrib = '/home/pi/namazTimes/maghribNotify.png'
    _imgSourceIscha = '/home/pi/namazTimes/ishaNotify.png'
else:
    _arialFont = '../fonts/arial.ttf'
    _fileName = 'log' + str(date.today()) + '.txt'
    _adhanAudio = './hayyaAllalSalah.mp3'

    _imgSourceFajr = './fajrNotify.png'
    _imgSourceDhuhr = './dhuhrNotify.png'
    _imgSourceAsr = './asrNotify.png'
    _imgSourceMaghrib = './maghribNotify.png'
    _imgSourceIscha = './ishaNotify.png'

if _write2file:
    with open(_fileName, 'a+') as filehandle:
        logMsg = str(datetime.now().strftime("%d-%m-%Y %H:%M:%S")) + str('Starting the prayer times system \n\n')
        filehandle.write(logMsg)


# Class communicating with SMART.kv file in folder
class NAMAZTIMESWidget(BoxLayout):

    def __init__(self, **kwargs):

        self._updateGUI_ClockEvent = []  # Clock triggering
        self._updateTime = 1  # Time in seconds after which new value will be received
        self._updateTimeNamaz = 3  # Time counter (multiple of updateTime) after which the namaz time should be updated
        self._timeCounter = 0  # Time counter to measure the elapsedTime
        self._firstStart = True  # Flag to check if its the first start

        ## Prayer Settings
        self._longitude = 11.62916  # Longitude of Magdeburg Germany
        self._latitude = 52.12773  # Latitude of Magdeburg Germany
        self._gmtToday = 1  # GMT zone of Germany (It differs in Winter and Summer, Winter = +1, Summer = +2)
        self._gmtTomorrow = 1  # GMT zone of Germany (It differs in Winter and Summer, Winter = +1, Summer = +2)
        self._summerTime = date.today()
        self._winterTime = date.today()
        self._isSummer = True  # Flag to check if its summer or winter time
        self._dayName = 'Fr'  # Name of the day if ii is Friday then Friday prayer will be highlighted not the Dhuhr
        self._hijriDate = str('1-Ramadan-1444')

        self._azaanTimesToday = []  # Array of azan times calculated - Today
        self._azaanTimesTomorrow = []  # Array of azan times calculated - Tomorrow
        self._azaanTimes = []  # Array of azaan times calculated
        self._jamaatTimes = []  # Array of jamaat times calculated
        self._prayerTimesOBJ = []  # Object of prayerTimes module

        ## Jamaat Settings - Jamaat after x minutes
        self._fajarJamaat = 30  # Fajar jamaat after 30 minutes of azaan
        self._delayJamaatMinutes_5 = 5  # Jamaat after 5 minutes maximum
        self._delayJamaatMinutes_10 = 10  # Jamaat after 10 minutes
        self._delayJamaatMinutes_30 = 30  # Jamaat after 30 minutes
        self._roundOffMinutes = 1  # roundOff the jamaat timing to the nearest roundOff minutes
        self._roundOffMinutesMaghrib = 1  # roundOff maghrib to nearest 5 minutes because time is very short
        self._roundOffMinutesJumma = 5  # roundOff Jumma to nearest 5 minutes

        ## Alarm/notification settings
        self._oldDate = date.today()  # record of old date
        self._notificationPopup = []  # notification popup
        self._isNotification = False  # flag that if notification is active
        self._notificationStartTime = tm.time()  # start time of notification
        self._notificationShowTime = 120  # notification show time in seconds

        ## AzanFlags
        self._azaanFlags = {'fajr': False, 'dhuhr': False, 'asr': False, 'maghrib': False, 'isha': False}

        return super(NAMAZTIMESWidget, self).__init__(**kwargs)

    # Configuration of scheduling events
    def showMainscreen(self, *args):
        # Configuring and setting the prayer table
        self.configPrayerTable()

        # Calling in function so that system will write configuration first
        self.configurePrayerTimes()

        # Getting ultrasonic data after a specific inteval
        self._updateGUI_ClockEvent = Clock.schedule_interval(self.updateGUI, self._updateTime)

    '''
        Configuring the prayer table. Text, fontstyle
    '''

    # Move to settings screen on button click
    def showSettingsScreen(self):
        self.ids.carousel.load_next()

    # Move to main screen
    def showMainScreen(self):
        self.ids.carousel.load_previous()

    def configPrayerTable(self):

        # Row 1 - Header
        self.ids.PrayerName.font_name = _arialFont

        Iqamah_Header_Text = arabic_reshaper.reshape("إقامة")
        Iqamah_Header_Text = bidi.algorithm.get_display(Iqamah_Header_Text)
        self.ids.Iqamah.text = "Iqamah-Zeit\n" + Iqamah_Header_Text
        self.ids.Iqamah.font_name = _arialFont

        Adhan_Header_Text = arabic_reshaper.reshape("وقت الأذان")
        Adhan_Header_Text = bidi.algorithm.get_display(Adhan_Header_Text)
        self.ids.Adhan.text = "Adhan-Zeit\n" + Adhan_Header_Text
        self.ids.Adhan.font_name = _arialFont

        PrayerName_AR_Header_Text = arabic_reshaper.reshape("الصلاة")
        PrayerName_AR_Header_Text = bidi.algorithm.get_display(PrayerName_AR_Header_Text)
        self.ids.PrayerName_AR.text = PrayerName_AR_Header_Text
        self.ids.PrayerName_AR.font_name = _arialFont

        # Row 2 - Fajr
        self.ids.Fajr.font_name = _arialFont
        self.ids.FajrAdhan.font_name = _arialFont
        self.ids.FajrIqamah.font_name = _arialFont

        Fajr_AR_Text = arabic_reshaper.reshape("الفجر")
        Fajr_AR_Text = bidi.algorithm.get_display(Fajr_AR_Text)
        self.ids.Fajr_AR.text = Fajr_AR_Text
        self.ids.Fajr_AR.font_name = _arialFont

        # Row 3 - Dhuhr
        self.ids.Dhuhr.font_name = _arialFont
        self.ids.DhuhrAdhan.font_name = _arialFont
        self.ids.DhuhrIqamah.font_name = _arialFont

        Dhuhr_AR_Text = arabic_reshaper.reshape("الظهر")
        Dhuhr_AR_Text = bidi.algorithm.get_display(Dhuhr_AR_Text)
        self.ids.Dhuhr_AR.text = Dhuhr_AR_Text
        self.ids.Dhuhr_AR.font_name = _arialFont

        # Row 4 - Asr
        self.ids.Asr.font_name = _arialFont
        self.ids.AsrAdhan.font_name = _arialFont
        self.ids.AsrIqamah.font_name = _arialFont

        Asr_AR_Text = arabic_reshaper.reshape("العصر")
        Asr_AR_Text = bidi.algorithm.get_display(Asr_AR_Text)
        self.ids.Asr_AR.text = Asr_AR_Text
        self.ids.Asr_AR.font_name = _arialFont

        # Row 5 - Maghrib
        self.ids.Maghrib.font_name = _arialFont
        self.ids.MaghribAdhan.font_name = _arialFont
        self.ids.MaghribIqamah.font_name = _arialFont

        Maghrib_AR_Text = arabic_reshaper.reshape("المغرب")
        Maghrib_AR_Text = bidi.algorithm.get_display(Maghrib_AR_Text)
        self.ids.Maghrib_AR.text = Maghrib_AR_Text
        self.ids.Maghrib_AR.font_name = _arialFont

        # Row 6 - Ischa
        self.ids.Ischa.font_name = _arialFont
        self.ids.IschaAdhan.font_name = _arialFont
        self.ids.IschaIqamah.font_name = _arialFont

        Ischa_AR_Text = arabic_reshaper.reshape("العشاء")
        Ischa_AR_Text = bidi.algorithm.get_display(Ischa_AR_Text)
        self.ids.Ischa_AR.text = Ischa_AR_Text
        self.ids.Ischa_AR.font_name = _arialFont

        # Row 7 - Jummah
        self.ids.Jummah.font_name = _arialFont
        self.ids.JummahAdhan.font_name = _arialFont
        self.ids.JummahIqamah.font_name = _arialFont

        Jummah_AR_Text = arabic_reshaper.reshape("الجمعة")
        Jummah_AR_Text = bidi.algorithm.get_display(Jummah_AR_Text)
        self.ids.Jummah_AR.text = Jummah_AR_Text
        self.ids.Jummah_AR.font_name = _arialFont

    '''
            Highlighting the current prayer time
    '''

    def highlightPrayerTime(self, currPrayer):

        defaultBackgroundColor = (0.5, 0.5, 0.5, 1)
        defaultFontColor = (1, 1, 1, 1)
        defaultFontSize = 40

        highlightBackgroundColor = (1, 0, 0, 1)
        highlightFontColor = (1, 1, 1, 1)
        highlightFontSize = 60

        # Fajr
        if currPrayer == 'Fajr':
            self.ids.Fajr.background_color = highlightBackgroundColor
            self.ids.FajrAdhan.background_color = highlightBackgroundColor
            self.ids.FajrIqamah.background_color = highlightBackgroundColor
            self.ids.Fajr_AR.background_color = highlightBackgroundColor

            self.ids.Fajr.font_size = highlightFontSize
            self.ids.FajrAdhan.font_size = highlightFontSize
            self.ids.FajrIqamah.font_size = highlightFontSize
            self.ids.Fajr_AR.font_size = highlightFontSize

            self.ids.Fajr.color = highlightFontColor
            self.ids.FajrAdhan.color = highlightFontColor
            self.ids.FajrIqamah.color = highlightFontColor
            self.ids.Fajr_AR.color = highlightFontColor
        else:
            self.ids.Fajr.background_color = defaultBackgroundColor
            self.ids.FajrAdhan.background_color = defaultBackgroundColor
            self.ids.FajrIqamah.background_color = defaultBackgroundColor
            self.ids.Fajr_AR.background_color = defaultBackgroundColor

            self.ids.Fajr.font_size = defaultFontSize
            self.ids.FajrAdhan.font_size = defaultFontSize
            self.ids.FajrIqamah.font_size = defaultFontSize
            self.ids.Fajr_AR.font_size = defaultFontSize

            self.ids.Fajr.color = defaultFontColor
            self.ids.FajrAdhan.color = defaultFontColor
            self.ids.FajrIqamah.color = defaultFontColor
            self.ids.Fajr_AR.color = defaultFontColor

        # Dhuhr / Jumma
        if currPrayer == 'Dhuhr':
            if self._dayName[:2] == 'Fr':
                # Highliht Freitagsgebet
                self.ids.Jummah.background_color = highlightBackgroundColor
                self.ids.JummahAdhan.background_color = highlightBackgroundColor
                self.ids.JummahIqamah.background_color = highlightBackgroundColor
                self.ids.Jummah_AR.background_color = highlightBackgroundColor

                self.ids.Jummah.font_size = 45  # Because if size is increased then it goes out of boundary
                self.ids.JummahAdhan.font_size = highlightFontSize
                self.ids.JummahIqamah.font_size = highlightFontSize
                self.ids.Jummah_AR.font_size = highlightFontSize

                self.ids.Jummah.color = highlightFontColor
                self.ids.JummahAdhan.color = highlightFontColor
                self.ids.JummahIqamah.color = highlightFontColor
                self.ids.Jummah_AR.color = highlightFontColor

                # Normalize Dhuhr
                self.ids.Dhuhr.background_color = defaultBackgroundColor
                self.ids.DhuhrAdhan.background_color = defaultBackgroundColor
                self.ids.DhuhrIqamah.background_color = defaultBackgroundColor
                self.ids.Dhuhr_AR.background_color = defaultBackgroundColor

                self.ids.Dhuhr.font_size = defaultFontSize
                self.ids.DhuhrAdhan.font_size = defaultFontSize
                self.ids.DhuhrIqamah.font_size = defaultFontSize
                self.ids.Dhuhr_AR.font_size = defaultFontSize

                self.ids.Dhuhr.color = defaultFontColor
                self.ids.DhuhrAdhan.color = defaultFontColor
                self.ids.DhuhrIqamah.color = defaultFontColor
                self.ids.Dhuhr_AR.color = defaultFontColor
            else:
                # Highlight Dhuhr
                self.ids.Dhuhr.background_color = highlightBackgroundColor
                self.ids.DhuhrAdhan.background_color = highlightBackgroundColor
                self.ids.DhuhrIqamah.background_color = highlightBackgroundColor
                self.ids.Dhuhr_AR.background_color = highlightBackgroundColor

                self.ids.Dhuhr.font_size = highlightFontSize
                self.ids.DhuhrAdhan.font_size = highlightFontSize
                self.ids.DhuhrIqamah.font_size = highlightFontSize
                self.ids.Dhuhr_AR.font_size = highlightFontSize

                self.ids.Dhuhr.color = highlightFontColor
                self.ids.DhuhrAdhan.color = highlightFontColor
                self.ids.DhuhrIqamah.color = highlightFontColor
                self.ids.Dhuhr_AR.color = highlightFontColor

                # Normalize Freitagsgebet
                self.ids.Jummah.background_color = defaultBackgroundColor
                self.ids.JummahAdhan.background_color = defaultBackgroundColor
                self.ids.JummahIqamah.background_color = defaultBackgroundColor
                self.ids.Jummah_AR.background_color = defaultBackgroundColor

                self.ids.Jummah.font_size = defaultFontSize
                self.ids.JummahAdhan.font_size = defaultFontSize
                self.ids.JummahIqamah.font_size = defaultFontSize
                self.ids.Jummah_AR.font_size = defaultFontSize

                self.ids.Jummah.color = defaultFontColor
                self.ids.JummahAdhan.color = defaultFontColor
                self.ids.JummahIqamah.color = defaultFontColor
                self.ids.Jummah_AR.color = defaultFontColor

        else:
            self.ids.Dhuhr.background_color = defaultBackgroundColor
            self.ids.DhuhrAdhan.background_color = defaultBackgroundColor
            self.ids.DhuhrIqamah.background_color = defaultBackgroundColor
            self.ids.Dhuhr_AR.background_color = defaultBackgroundColor

            self.ids.Dhuhr.font_size = defaultFontSize
            self.ids.DhuhrAdhan.font_size = defaultFontSize
            self.ids.DhuhrIqamah.font_size = defaultFontSize
            self.ids.Dhuhr_AR.font_size = defaultFontSize

            self.ids.Dhuhr.color = defaultFontColor
            self.ids.DhuhrAdhan.color = defaultFontColor
            self.ids.DhuhrIqamah.color = defaultFontColor
            self.ids.Dhuhr_AR.color = defaultFontColor

        # Asr
        if currPrayer == 'Asr':
            self.ids.Asr.background_color = highlightBackgroundColor
            self.ids.AsrAdhan.background_color = highlightBackgroundColor
            self.ids.AsrIqamah.background_color = highlightBackgroundColor
            self.ids.Asr_AR.background_color = highlightBackgroundColor

            self.ids.Asr.font_size = highlightFontSize
            self.ids.AsrAdhan.font_size = highlightFontSize
            self.ids.AsrIqamah.font_size = highlightFontSize
            self.ids.Asr_AR.font_size = highlightFontSize

            self.ids.Asr.color = highlightFontColor
            self.ids.AsrAdhan.color = highlightFontColor
            self.ids.AsrIqamah.color = highlightFontColor
            self.ids.Asr_AR.color = highlightFontColor
        else:
            self.ids.Asr.background_color = defaultBackgroundColor
            self.ids.AsrAdhan.background_color = defaultBackgroundColor
            self.ids.AsrIqamah.background_color = defaultBackgroundColor
            self.ids.Asr_AR.background_color = defaultBackgroundColor

            self.ids.Asr.font_size = defaultFontSize
            self.ids.AsrAdhan.font_size = defaultFontSize
            self.ids.AsrIqamah.font_size = defaultFontSize
            self.ids.Asr_AR.font_size = defaultFontSize

            self.ids.Asr.color = defaultFontColor
            self.ids.AsrAdhan.color = defaultFontColor
            self.ids.AsrIqamah.color = defaultFontColor
            self.ids.Asr_AR.color = defaultFontColor

        # Maghrib
        if currPrayer == 'Maghrib':
            self.ids.Maghrib.background_color = highlightBackgroundColor
            self.ids.MaghribAdhan.background_color = highlightBackgroundColor
            self.ids.MaghribIqamah.background_color = highlightBackgroundColor
            self.ids.Maghrib_AR.background_color = highlightBackgroundColor

            self.ids.Maghrib.font_size = highlightFontSize
            self.ids.MaghribAdhan.font_size = highlightFontSize
            self.ids.MaghribIqamah.font_size = highlightFontSize
            self.ids.Maghrib_AR.font_size = highlightFontSize

            self.ids.Maghrib.color = highlightFontColor
            self.ids.MaghribAdhan.color = highlightFontColor
            self.ids.MaghribIqamah.color = highlightFontColor
            self.ids.Maghrib_AR.color = highlightFontColor
        else:
            self.ids.Maghrib.background_color = defaultBackgroundColor
            self.ids.MaghribAdhan.background_color = defaultBackgroundColor
            self.ids.MaghribIqamah.background_color = defaultBackgroundColor
            self.ids.Maghrib_AR.background_color = defaultBackgroundColor

            self.ids.Maghrib.font_size = defaultFontSize
            self.ids.MaghribAdhan.font_size = defaultFontSize
            self.ids.MaghribIqamah.font_size = defaultFontSize
            self.ids.Maghrib_AR.font_size = defaultFontSize

            self.ids.Maghrib.color = defaultFontColor
            self.ids.MaghribAdhan.color = defaultFontColor
            self.ids.MaghribIqamah.color = defaultFontColor
            self.ids.Maghrib_AR.color = defaultFontColor

        # Ischa
        if currPrayer == 'Ischa':
            self.ids.Ischa.background_color = highlightBackgroundColor
            self.ids.IschaAdhan.background_color = highlightBackgroundColor
            self.ids.IschaIqamah.background_color = highlightBackgroundColor
            self.ids.Ischa_AR.background_color = highlightBackgroundColor

            self.ids.Ischa.font_size = highlightFontSize
            self.ids.IschaAdhan.font_size = highlightFontSize
            self.ids.IschaIqamah.font_size = highlightFontSize
            self.ids.Ischa_AR.font_size = highlightFontSize

            self.ids.Ischa.color = highlightFontColor
            self.ids.IschaAdhan.color = highlightFontColor
            self.ids.IschaIqamah.color = highlightFontColor
            self.ids.Ischa_AR.color = highlightFontColor
        else:
            self.ids.Ischa.background_color = defaultBackgroundColor
            self.ids.IschaAdhan.background_color = defaultBackgroundColor
            self.ids.IschaIqamah.background_color = defaultBackgroundColor
            self.ids.Ischa_AR.background_color = defaultBackgroundColor

            self.ids.Ischa.font_size = defaultFontSize
            self.ids.IschaAdhan.font_size = defaultFontSize
            self.ids.IschaIqamah.font_size = defaultFontSize
            self.ids.Ischa_AR.font_size = defaultFontSize

            self.ids.Ischa.color = defaultFontColor
            self.ids.IschaAdhan.color = defaultFontColor
            self.ids.IschaIqamah.color = defaultFontColor
            self.ids.Ischa_AR.color = defaultFontColor

    '''
    Show popup displaying the name of the current azan time
    '''

    def notifyPopup(self, imageName):

        imgSource = ""

        # Name of the image to be loaded
        if imageName == 'fajr':
            imgSource = _imgSourceFajr
        elif imageName == 'dhuhr':
            imgSource = _imgSourceDhuhr
        elif imageName == 'asr':
            imgSource = _imgSourceAsr
        elif imageName == 'maghrib':
            imgSource = _imgSourceMaghrib
        elif imageName == 'isha':
            imgSource = _imgSourceIscha

        self._notificationPopup = Popup(title='Notification',
                                        content=Image(source=imgSource),
                                        size_hint=(None, None), size=(600, 600), auto_dismiss=False)

        # Open the notification
        self._notificationPopup.open()
        self._isNotification = True
        self._notificationStartTime = tm.time()

        # play azan sound
        self.playAzan()

        # writing to log file
        if _write2file:
            logMsg = str(datetime.now().strftime("%d-%m-%Y %H:%M:%S")) + str(' : Notification for ') + str(
                imageName) + str('\n')
            with open(_fileName, 'a+') as filehandle:
                filehandle.write(logMsg)

    '''
    Play azan sound
    '''

    def playAzan(self, *args):

        # azan alarm
        pygame.mixer.init()
        pygame.mixer.music.load(_adhanAudio)
        pygame.mixer.music.play()

        while pygame.mixer.music.get_busy() == True:
            continue

    '''
    Check if its azan time then play the azan sound
    '''

    def notifyAzan(self, *args):

        currTime = datetime.now().strftime("%H:%M")

        if not self._firstStart:
            if not self._azaanFlags['fajr']:
                if self.isAzanTime(str(self._azaanTimes['fajr']), str(currTime)):
                    self._azaanFlags['fajr'] = True
                    self.highlightPrayerTime('Fajr')
                    self.notifyPopup('fajr')

            if not self._azaanFlags['dhuhr']:
                if self.isAzanTime(str(self._azaanTimes['dhuhr']), str(currTime)):
                    self._azaanFlags['dhuhr'] = True
                    self.highlightPrayerTime('Dhuhr')
                    self.notifyPopup('dhuhr')

            if not self._azaanFlags['asr']:
                if self.isAzanTime(str(self._azaanTimes['asr']), str(currTime)):
                    self._azaanFlags['asr'] = True
                    self.highlightPrayerTime('Asr')
                    self.notifyPopup('asr')

            if not self._azaanFlags['maghrib']:
                if self.isAzanTime(str(self._azaanTimes['maghrib']), str(currTime)):
                    self._azaanFlags['maghrib'] = True
                    self.highlightPrayerTime('Maghrib')
                    self.notifyPopup('maghrib')

            if not self._azaanFlags['isha']:
                if self.isAzanTime(str(self._azaanTimes['isha']), str(currTime)):
                    self._azaanFlags['isha'] = True
                    self.highlightPrayerTime('Ischa')
                    self.notifyPopup('isha')

    '''
    Check if time is matched
    '''

    def isAzanTime(self, scheduledTime, currTime):
        isTime = False

        azan = re.split(':', str(scheduledTime))
        curr = re.split(':', str(currTime))

        if (int(azan[0]) == int(curr[0])) and (int(azan[1]) == int(curr[1])):
            isTime = True

        return isTime

    '''
    Get the last sunday of March and October
    Because in Germany Summer and Winter time change occurs in these months
    '''

    def getLastSundayDate(self, todayYear):

        summerTime_Day = max(week[-1] for week in calendar.monthcalendar(todayYear, 3))

        winterTime_Day = max(week[-1] for week in calendar.monthcalendar(todayYear, 10))

        return summerTime_Day, winterTime_Day

    # Update the App GUI
    def updateGUI(self, *args):

        self._timeCounter = self._timeCounter + 1

        self.notifyAzan()

        # If notification is open then wait and close it
        if self._isNotification:
            if tm.time() - self._notificationStartTime >= self._notificationShowTime:
                self._notificationPopup.dismiss()
                self._isNotification = False

        _today = date.today()
        _yearToday = _today.year
        _monthToday = _today.month
        _dayToday = _today.day

        _tomorrow = _today + timedelta(1)
        _yearTomorrow = _tomorrow.year
        _monthTomorrow = _tomorrow.month
        _dayTomorrow = _tomorrow.day

        hijriToday = Gregorian(_today.year, _today.month, _today.day).to_hijri()
        self._hijriDate = str(hijriToday.day) + str('-') + str(hijriToday.month_name()) + str('-') + str(
            hijriToday.year)

        # Time change dates of the year
        summerTimeDay, winterTimeDay = self.getLastSundayDate(_yearToday)

        self._summerTime = date(_yearToday, 3, summerTimeDay)
        self._winterTime = date(_yearToday, 10, winterTimeDay)

        currentTime = datetime.now().strftime("%H:%M:%S")
        currentDate = date(_yearToday, _monthToday, _dayToday)
        dayName_en = str(calendar.day_name[currentDate.weekday()])

        if dayName_en == 'Monday':
            self._dayName = 'Montag'
        elif dayName_en == 'Tuesday':
            self._dayName = 'Dienstag'
        elif dayName_en == 'Wednesday':
            self._dayName = 'Mittwoch'
        elif dayName_en == 'Thursday':
            self._dayName = 'Donnerstag'
        elif dayName_en == 'Friday':
            self._dayName = 'Freitag'
        elif dayName_en == 'Saturday':
            self._dayName = 'Samstag'
        elif dayName_en == 'Sunday':
            self._dayName = 'Sonntag'

        if self._summerTime <= _today < self._winterTime:
            self._isSummer = True
            self._gmtToday = 2
            self._gmtTomorrow = self._gmtToday
        else:  # Winter Time
            self._isSummer = False
            self._gmtToday = 1
            self._gmtTomorrow = self._gmtToday

        # Update the time for tomorrow
        if _tomorrow == self._summerTime:
            self._gmtTomorrow = 2
        elif _tomorrow == self._winterTime:
            self._gmtTomorrow = 1

        # if new day then reset all flags
        if self._oldDate != _today:
            self._oldDate = _today
            self._azaanFlags['fajr'] = False
            self._azaanFlags['dhuhr'] = False
            self._azaanFlags['asr'] = False
            self._azaanFlags['maghrib'] = False
            self._azaanFlags['isha'] = False

        '''
        Update date and time of the GUI
        '''
        self.ids.time_Label.text = str(currentTime)
        self.ids.date_Label.text = self._dayName + str(', ') + str(_dayToday) + str('.') + str(_monthToday) + str(
            '.') + str(_yearToday)
        self.ids.dateHijri_Label.text = self._hijriDate

        if self._firstStart or (self._timeCounter % self._updateTimeNamaz) == 0:
            self._firstStart = False

            if (self._timeCounter % self._updateTimeNamaz) == 0:
                self._timeCounter = 0

            self._azaanTimesToday = self._prayerTimesOBJ.get_times(date(_yearToday, _monthToday, _dayToday),
                                                                   (self._latitude, self._longitude), self._gmtToday)
            self._azaanTimesTomorrow = self._prayerTimesOBJ.get_times(date(_yearTomorrow, _monthTomorrow, _dayTomorrow),
                                                                      (self._latitude, self._longitude),
                                                                      self._gmtTomorrow)

            # Calculate jamaat times
            self._azaanTimes = self._azaanTimesToday
            self._jamaatTimes = self.compute_prayerJamaat_times()

            # Move to the next screen
            #self.ids.carousel.load_next()

            # Updating the times
            self.ids.FajrAdhan.text = str(self._azaanTimes['fajr'])
            self.ids.DhuhrAdhan.text = str(self._azaanTimes['dhuhr'])
            self.ids.AsrAdhan.text = str(self._azaanTimes['asr'])
            self.ids.MaghribAdhan.text = str(self._azaanTimes['maghrib'])
            self.ids.IschaAdhan.text = str(self._azaanTimes['isha'])
            self.ids.JummahAdhan.text = str(self._azaanTimes['dhuhr'])

            ## Sahoor and Shurooq Time
            Imsak_Label_Text = arabic_reshaper.reshape("السحور")
            Imsak_Label_Text = bidi.algorithm.get_display(Imsak_Label_Text)
            Imsak_Label_Text = "Imsak (" + Imsak_Label_Text + (') - ') + str(self._azaanTimes['imsak'])
            self.ids.imsak_Label.font_name = _arialFont
            self.ids.imsak_Label.text = Imsak_Label_Text

            Sunrise_Label_Text = arabic_reshaper.reshape("الشروق")
            Sunrise_Label_Text = bidi.algorithm.get_display(Sunrise_Label_Text)
            Sunrise_Label_Text = "Sonnenaufgang (" + Sunrise_Label_Text + (') - ') + str(self._azaanTimes['sunrise'])
            self.ids.sunrise_Label.font_name = _arialFont
            self.ids.sunrise_Label.text = Sunrise_Label_Text

            ## Updating Jamaat Times
            self.ids.FajrIqamah.text = str(self._jamaatTimes['fajr'])
            self.ids.DhuhrIqamah.text = str(self._jamaatTimes['dhuhr'])
            self.ids.AsrIqamah.text = str(self._jamaatTimes['asr'])
            self.ids.MaghribIqamah.text = str(self._jamaatTimes['maghrib'])
            self.ids.IschaIqamah.text = str(self._jamaatTimes['isha'])
            self.ids.JummahIqamah.text = str(self._jamaatTimes['jumma'])

    '''
     Compute the jamaat (Iqama) times of all the 5 prayers based on the jamaat times after the azaan

     If jamaat time of today's prayer has passed then update the time to tomorrow's time
    '''

    def compute_prayerJamaat_times(self):
        ## FAJR
        fajrAzan = re.split(':', self._azaanTimesToday['fajr'])
        fajrTime = time(int(fajrAzan[0]), int(fajrAzan[1]))
        fajrJamaat = ((datetime.combine(date.today(), fajrTime)))
        fajrRounded = self.roundTime(fajrJamaat, self._fajarJamaat, self._roundOffMinutes)

        if datetime.now() > fajrRounded:
            fajrAzan = re.split(':', self._azaanTimesTomorrow['fajr'])
            fajrTime = time(int(fajrAzan[0]), int(fajrAzan[1]))
            fajrJamaat = ((datetime.combine(date.today(), fajrTime)))
            fajrRounded = self.roundTime(fajrJamaat, self._fajarJamaat, self._roundOffMinutes)
            fajr = fajrRounded.strftime('%H:%M')

            self._azaanTimes['fajr'] = self._azaanTimesTomorrow['fajr']
            self._azaanTimes['imsak'] = self._azaanTimesTomorrow['imsak']
        else:
            fajr = fajrRounded.strftime('%H:%M')

        ## SHUROOQ
        Shurooq = re.split(':', self._azaanTimesToday['sunrise'])
        ShurooqTime = time(int(Shurooq[0]), int(Shurooq[1]))
        ShurooqDateTime = ((datetime.combine(date.today(), ShurooqTime)))

        if datetime.now() > ShurooqDateTime:
            Shurooq = re.split(':', self._azaanTimesTomorrow['sunrise'])
            ShurooqTime = time(int(Shurooq[0]), int(Shurooq[1]))
            ShurooqDateTime = ((datetime.combine(date.today(), ShurooqTime)))

            self._azaanTimes['sunrise'] = self._azaanTimesTomorrow['sunrise']

        ## DHUHR
        dhuhrAzan = re.split(':', self._azaanTimesToday['dhuhr'])
        dhuhrTime = time(int(dhuhrAzan[0]), int(dhuhrAzan[1]))
        dhuhrJamaat = ((datetime.combine(date.today(), dhuhrTime)))
        dhuhrRounded = self.roundTime(dhuhrJamaat, self._delayJamaatMinutes_10, self._roundOffMinutes)

        if datetime.now() > dhuhrRounded:
            dhuhrAzan = re.split(':', self._azaanTimesTomorrow['dhuhr'])
            dhuhrTime = time(int(dhuhrAzan[0]), int(dhuhrAzan[1]))
            dhuhrJamaat = ((datetime.combine(date.today(), dhuhrTime)))
            dhuhrRounded = self.roundTime(dhuhrJamaat, self._delayJamaatMinutes_10, self._roundOffMinutes)
            dhuhr = dhuhrRounded.strftime('%H:%M')

            self._azaanTimes['dhuhr'] = self._azaanTimesTomorrow['dhuhr']
        else:
            dhuhr = dhuhrRounded.strftime('%H:%M')

        ## ASR
        asrAzan = re.split(':', self._azaanTimesToday['asr'])
        asrTime = time(int(asrAzan[0]), int(asrAzan[1]))
        asrJamaat = ((datetime.combine(date.today(), asrTime)))
        asrRounded = self.roundTime(asrJamaat, self._delayJamaatMinutes_5, self._roundOffMinutes)

        if datetime.now() > asrRounded:
            asrAzan = re.split(':', self._azaanTimesTomorrow['asr'])
            asrTime = time(int(asrAzan[0]), int(asrAzan[1]))
            asrJamaat = ((datetime.combine(date.today(), asrTime)))
            asrRounded = self.roundTime(asrJamaat, self._delayJamaatMinutes_5, self._roundOffMinutes)
            asr = asrRounded.strftime('%H:%M')

            self._azaanTimes['asr'] = self._azaanTimesTomorrow['asr']
        else:
            asr = asrRounded.strftime('%H:%M')

        ## MAGHRIB
        maghribAzan = re.split(':', self._azaanTimesToday['maghrib'])
        maghribTime = time(int(maghribAzan[0]), int(maghribAzan[1]))
        maghribJamaat = ((datetime.combine(date.today(), maghribTime)))
        maghribRounded = self.roundTime(maghribJamaat, self._delayJamaatMinutes_5, self._roundOffMinutesMaghrib)

        if datetime.now() > maghribRounded:
            maghribAzan = re.split(':', self._azaanTimesTomorrow['maghrib'])
            maghribTime = time(int(maghribAzan[0]), int(maghribAzan[1]))
            maghribJamaat = ((datetime.combine(date.today(), maghribTime)))
            maghribRounded = self.roundTime(maghribJamaat, self._delayJamaatMinutes_5, self._roundOffMinutesMaghrib)
            maghrib = maghribRounded.strftime('%H:%M')

            self._azaanTimes['maghrib'] = self._azaanTimesTomorrow['maghrib']
        else:
            maghrib = maghribRounded.strftime('%H:%M')

        ## ISHA
        ishaAzan = re.split(':', self._azaanTimesToday['isha'])
        ishaTime = time(int(ishaAzan[0]), int(ishaAzan[1]))
        ishaJamaat = ((datetime.combine(date.today(), ishaTime)))
        ishaRounded = self.roundTime(ishaJamaat, self._delayJamaatMinutes_5, self._roundOffMinutes)

        if datetime.now() > ishaRounded:
            ishaAzan = re.split(':', self._azaanTimesTomorrow['isha'])
            ishaTime = time(int(ishaAzan[0]), int(ishaAzan[1]))
            ishaJamaat = ((datetime.combine(date.today(), ishaTime)))
            ishaRounded = self.roundTime(ishaJamaat, self._delayJamaatMinutes_5, self._roundOffMinutes)
            isha = ishaRounded.strftime('%H:%M')

            self._azaanTimes['isha'] = self._azaanTimesTomorrow['isha']
        else:
            isha = ishaRounded.strftime('%H:%M')

        ## JUMMA
        jummaAzan = re.split(':', self._azaanTimesToday['dhuhr'])
        jummaTime = time(int(jummaAzan[0]), int(jummaAzan[1]))
        jummaJamaat = ((datetime.combine(date.today(), jummaTime)))
        jummaRounded = self.roundTime(jummaJamaat, self._delayJamaatMinutes_30, self._roundOffMinutesJumma)

        if datetime.now() > dhuhrRounded:
            jummaAzan = re.split(':', self._azaanTimesTomorrow['dhuhr'])
            jummaTime = time(int(jummaAzan[0]), int(jummaAzan[1]))
            jummaJamaat = ((datetime.combine(date.today(), jummaTime)))
            jummaRounded = self.roundTime(jummaJamaat, self._delayJamaatMinutes_30, self._roundOffMinutesJumma)
            jumma = jummaRounded.strftime('%H:%M')

            self._azaanTimes['jumma'] = self._azaanTimesTomorrow['dhuhr']
        else:
            jumma = jummaRounded.strftime('%H:%M')

        return {
            'fajr': fajr, 'dhuhr': dhuhr, 'asr': asr, 'maghrib': maghrib, 'isha': isha, 'jumma': jumma
        }

    # round off the jamaat time to the nearest self._roundOffMinutes
    def roundTime(self, dt, delayJamaat, roundOf):

        approx = math.ceil((dt.minute + delayJamaat) / roundOf) * roundOf
        dt = dt.replace(minute=0)
        dt += timedelta(seconds=(approx) * 60)

        roundedTime = dt

        return roundedTime

    # Reseting the GUI
    def resetGUI(self, *args):
        pass

    # Configuration of settings of the prayer times
    def configurePrayerTimes(self, *args):

        self._prayerTimesOBJ = pT.PrayTimes('MWL')
        self._prayerTimesOBJ.time_format = '24h'

        self._prayerTimesOBJ.adjust({'fajr': 10})
        self._prayerTimesOBJ.adjust({'isha': '90 minutes'})
        self._prayerTimesOBJ.adjust({'imsak': 18})
        self._prayerTimesOBJ.adjust({'asr': 'Standard'})  # Method can be [Standard or Hanafi]
        self._prayerTimesOBJ.adjust({'dhuhr': '5 min'})  # Dhuhr time 5 minutes after zawal
        self._prayerTimesOBJ.adjust({'maghrib': '7 min'})  # Maghrib time 7 minutes after sunset


# Main App class
# Starting the mainscreen update as App loads
# Simple Smart Solutions (SSS) SMARTApp
class NAMAZTIMESApp(App):
    def build(self):
        # global _updateGUI_ClockEvent

        NAMAZTIMESW = NAMAZTIMESWidget()

        # Start the mainscreen as the Display is turned ON
        self._updateGUI_ClockEvent = Clock.schedule_once(NAMAZTIMESW.showMainscreen)

        return NAMAZTIMESW


if __name__ == "__main__":
    NAMAZTIMESApp().run()
