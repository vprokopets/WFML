# Generated by Selenium IDE
import pytest
import time
import json
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.common.action_chains import ActionChains
from selenium.webdriver.support import expected_conditions
from selenium.webdriver.support.wait import WebDriverWait
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.common.desired_capabilities import DesiredCapabilities

class TestSTD():
  def setup_method(self, method):
    self.driver = webdriver.Firefox(executable_path=r'geckodriver')
    self.vars = {}
  
  def teardown_method(self, method):
    self.driver.quit()
  
  def test_sTD(self):
    # Test name: STD
    # Step # | name | target | value
    # 1 | open | /wizard/test/ | 
    self.driver.get("http://127.0.0.1:8000/wizard/test/")
    # 2 | setWindowSize | 1853x1053 | 
    self.driver.set_window_size(1853, 1053)
    # 3 | click | css=input:nth-child(3) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(3)").click()
    # 4 | click | id=id_0-fcard_Predictor.Models | 
    self.driver.find_element(By.ID, "id_0-fcard_Predictor.Models").click()
    # 5 | type | id=id_0-fcard_Predictor.Models | 2
    self.driver.find_element(By.ID, "id_0-fcard_Predictor.Models").send_keys("2")
    # 6 | type | id=id_0-fcard_QuantityBasedSC | 1
    self.driver.find_element(By.ID, "id_0-fcard_QuantityBasedSC").send_keys("1")
    # 7 | type | id=id_0-fcard_BadConfigurationBasedSC | 1
    self.driver.find_element(By.ID, "id_0-fcard_BadConfigurationBasedSC").send_keys("1")
    # 8 | type | id=id_0-fcard_ImprovementBasedSC | 1
    self.driver.find_element(By.ID, "id_0-fcard_ImprovementBasedSC").send_keys("1")
    # 9 | type | id=id_0-fcard_TimeBasedSC | 2
    self.driver.find_element(By.ID, "id_0-fcard_TimeBasedSC").send_keys("2")
    # 10 | click | css=input:nth-child(8) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(8)").click()
    # 11 | click | css=li:nth-child(1) > label | 
    self.driver.find_element(By.CSS_SELECTOR, "li:nth-child(1) > label").click()
    # 12 | click | css=li:nth-child(3) > label | 
    self.driver.find_element(By.CSS_SELECTOR, "li:nth-child(3) > label").click()
    # 13 | click | css=li:nth-child(5) > label | 
    self.driver.find_element(By.CSS_SELECTOR, "li:nth-child(5) > label").click()
    # 14 | click | id=id_1-gcard_Repeater | 
    self.driver.find_element(By.ID, "id_1-gcard_Repeater").click()
    # 15 | click | css=#id_1-gcard_Repeater > option:nth-child(1) | 
    self.driver.find_element(By.CSS_SELECTOR, "#id_1-gcard_Repeater > option:nth-child(1)").click()

    # 16 | click | id=id_1-gcard_Predictor.Models_0 | 
    self.driver.find_element(By.ID, "id_1-gcard_Predictor.Models_0").click()
    # 17 | click | css=#id_1-gcard_Predictor\.Models_0 > option:nth-child(1) | 
    self.driver.find_element(By.CSS_SELECTOR, "#id_1-gcard_Predictor\\.Models_0 > option:nth-child(1)").click()
    # 18 | click | id=id_1-gcard_Predictor.Models_1 | 
    self.driver.find_element(By.ID, "id_1-gcard_Predictor.Models_1").click()
    # 19 | select | id=id_1-gcard_Predictor.Models_1 | label=MAB
    dropdown = self.driver.find_element(By.ID, "id_1-gcard_Predictor.Models_1")
    dropdown.find_element(By.XPATH, "//option[. = 'MAB']").click()
    # 19 | select | id=id_1-gcard_Predictor.Models_1 | label=MAB
    dropdown = self.driver.find_element(By.ID, "id_1-gcard_Predictor.Models_0")
    dropdown.find_element(By.XPATH, "//option[. = 'TPE']").click()
    # 20 | click | css=#id_1-gcard_Predictor\.Models_1 > option:nth-child(2) | 
    self.driver.find_element(By.CSS_SELECTOR, "#id_1-gcard_Predictor\\.Models_1 > option:nth-child(2)").click()
    # 21 | click | id=id_1-gcard_Predictor.Models_1.MAB.Parameters.cType | 
    self.driver.find_element(By.ID, "id_1-gcard_Predictor.Models_1.MAB.Parameters.cType").click()
    # 22 | select | id=id_1-gcard_Predictor.Models_1.MAB.Parameters.cType | label=float
    dropdown = self.driver.find_element(By.ID, "id_1-gcard_Predictor.Models_1.MAB.Parameters.cType")
    dropdown.find_element(By.XPATH, "//option[. = 'float']").click()
    # 22.5 | select | id=id_1-gcard_Predictor.Models_0.MAB.Parameters.cType | label=int
    dropdown = self.driver.find_element(By.ID, "id_1-gcard_Predictor.Models_0.MAB.Parameters.cType")
    dropdown.find_element(By.XPATH, "//option[. = 'int']").click()
    # 23 | click | css=#id_1-gcard_Predictor\.Models_1\.MAB\.Parameters\.cType > option:nth-child(2) | 
    self.driver.find_element(By.CSS_SELECTOR, "#id_1-gcard_Predictor\\.Models_1\\.MAB\\.Parameters\\.cType > option:nth-child(2)").click()
    # 24 | click | css=input:nth-child(11) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(11)").click()
    # 25 | type | id=id_2-TimeBasedSC_0.Name | TBSC0
    self.driver.find_element(By.ID, "id_2-TimeBasedSC_0.Name").send_keys("TBSC0")
    # 26 | type | id=id_2-TimeBasedSC_0.Parameters.MaxRunTime | 10
    self.driver.find_element(By.ID, "id_2-TimeBasedSC_0.Parameters.MaxRunTime").send_keys("10")
    # 27 | type | id=id_2-TimeBasedSC_0.Parameters.TimeUnit | m
    self.driver.find_element(By.ID, "id_2-TimeBasedSC_0.Parameters.TimeUnit").send_keys("m")
    # 28 | type | id=id_2-TimeBasedSC_1.Name | TBSC1
    self.driver.find_element(By.ID, "id_2-TimeBasedSC_1.Name").send_keys("TBSC1")
    # 29 | type | id=id_2-TimeBasedSC_1.Parameters.MaxRunTime | 1
    self.driver.find_element(By.ID, "id_2-TimeBasedSC_1.Parameters.MaxRunTime").send_keys("1")
    # 30 | type | id=id_2-TimeBasedSC_1.Parameters.TimeUnit | h
    self.driver.find_element(By.ID, "id_2-TimeBasedSC_1.Parameters.TimeUnit").send_keys("h")
    # 31 | click | css=input:nth-child(11) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(11)").click()
    # 32 | type | id=id_3-ImprovementBasedSC.Name | IBSC
    self.driver.find_element(By.ID, "id_3-ImprovementBasedSC.Name").send_keys("IBSC")
    # 33 | type | id=id_3-ImprovementBasedSC.Parameters.MaxConfigsWithoutImprovement | 5
    self.driver.find_element(By.ID, "id_3-ImprovementBasedSC.Parameters.MaxConfigsWithoutImprovement").send_keys("5")
    # 34 | click | css=input:nth-child(7) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(7)").click()
    # 35 | type | id=id_4-BadConfigurationBasedSC.Name | BCBSC
    self.driver.find_element(By.ID, "id_4-BadConfigurationBasedSC.Name").send_keys("BCBSC")
    # 36 | type | id=id_4-BadConfigurationBasedSC.Parameters.MaxBadConfigurations | 20
    self.driver.find_element(By.ID, "id_4-BadConfigurationBasedSC.Parameters.MaxBadConfigurations").send_keys("20")
    # 37 | click | css=input:nth-child(7) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(7)").click()
    # 38 | type | id=id_5-GuaranteedSC.Name | GSC
    self.driver.find_element(By.ID, "id_5-GuaranteedSC.Name").send_keys("GSC")
    # 39 | click | css=input:nth-child(6) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(6)").click()
    # 40 | type | id=id_6-QuantityBasedSC.Name | QBSC
    self.driver.find_element(By.ID, "id_6-QuantityBasedSC.Name").send_keys("QBSC")
    # 41 | type | id=id_6-QuantityBasedSC.Parameters.MaxConfigs | 5
    self.driver.find_element(By.ID, "id_6-QuantityBasedSC.Parameters.MaxConfigs").send_keys("5")
    # 42 | click | css=input:nth-child(7) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(7)").click()
    # 43 | type | id=id_7-StopConditionTriggerLogic.Expression | (QuantityBased and Guaranteed and ImprovementBased) or BadConfigurationBased or TimeBased
    self.driver.find_element(By.ID, "id_7-StopConditionTriggerLogic.Expression").send_keys("(QuantityBased and Guaranteed and ImprovementBased) or BadConfigurationBased or TimeBased")
    # 44 | type | id=id_7-StopConditionTriggerLogic.InspectionParameters.RepetitionPerion | 1
    self.driver.find_element(By.ID, "id_7-StopConditionTriggerLogic.InspectionParameters.RepetitionPerion").send_keys("1")
    # 45 | type | id=id_7-StopConditionTriggerLogic.InspectionParameters.TimeUnit | s
    self.driver.find_element(By.ID, "id_7-StopConditionTriggerLogic.InspectionParameters.TimeUnit").send_keys("s")
    # 46 | click | css=input:nth-child(8) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(8)").click()
    # 47 | type | id=id_8-Predictor.Models_0.TPE.Parameters.BandwidthFactor | 3
    self.driver.find_element(By.ID, "id_8-Predictor.Models_0.TPE.Parameters.BandwidthFactor").send_keys("3")
    # 48 | type | id=id_8-Predictor.Models_0.TPE.Parameters.MinBandwirth | 0
    self.driver.find_element(By.ID, "id_8-Predictor.Models_0.TPE.Parameters.MinBandwirth").send_keys("0")
    # 49 | type | id=id_8-Predictor.Models_0.TPE.Parameters.RandomFraction | 0
    self.driver.find_element(By.ID, "id_8-Predictor.Models_0.TPE.Parameters.RandomFraction").send_keys("0")
    # 50 | type | id=id_8-Predictor.Models_0.TPE.Parameters.SamplingSize | 96
    self.driver.find_element(By.ID, "id_8-Predictor.Models_0.TPE.Parameters.SamplingSize").send_keys("96")
    # 51 | type | id=id_8-Predictor.Models_0.TPE.Parameters.TopNPercent | 30
    self.driver.find_element(By.ID, "id_8-Predictor.Models_0.TPE.Parameters.TopNPercent").send_keys("30")
    # 52 | type | id=id_8-Predictor.Models_1.MAB.Parameters.c | 0.5
    self.driver.find_element(By.ID, "id_8-Predictor.Models_1.MAB.Parameters.c").send_keys("0.5")
    # 53 | type | id=id_8-Predictor.WindowSize | 0.5
    self.driver.find_element(By.ID, "id_8-Predictor.WindowSize").send_keys("0.5")
    # 54 | click | css=input:nth-child(12) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(12)").click()
    # 55 | type | id=id_9-Repeater.DefaultRepeater.MaxTasksPerConfiguration | 10
    self.driver.find_element(By.ID, "id_9-Repeater.DefaultRepeater.MaxTasksPerConfiguration").send_keys("10")
    # 56 | type | id=id_9-Repeater.DefaultRepeater.MinTasksPerConfiguration | 2
    self.driver.find_element(By.ID, "id_9-Repeater.DefaultRepeater.MinTasksPerConfiguration").send_keys("2")
    # 57 | click | css=input:nth-child(7) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(7)").click()
    # 58 | type | id=id_10-OD.Chauvenet.MaxActiveNumberOfTasks | 30
    self.driver.find_element(By.ID, "id_10-OD.Chauvenet.MaxActiveNumberOfTasks").send_keys("30")
    # 59 | type | id=id_10-OD.Chauvenet.MinActiveNumberOfTasks | 3
    self.driver.find_element(By.ID, "id_10-OD.Chauvenet.MinActiveNumberOfTasks").send_keys("3")
    # 60 | type | id=id_10-OD.Dixon.MaxActiveNumberOfTasks | 30
    self.driver.find_element(By.ID, "id_10-OD.Dixon.MaxActiveNumberOfTasks").send_keys("30")
    # 61 | type | id=id_10-OD.Dixon.MinActiveNumberOfTasks | 3
    self.driver.find_element(By.ID, "id_10-OD.Dixon.MinActiveNumberOfTasks").send_keys("3")
    # 62 | type | id=id_10-OD.Mad.MaxActiveNumberOfTasks | 30
    self.driver.find_element(By.ID, "id_10-OD.Mad.MaxActiveNumberOfTasks").send_keys("30")
    # 63 | type | id=id_10-OD.Mad.MinActiveNumberOfTasks | 3
    self.driver.find_element(By.ID, "id_10-OD.Mad.MinActiveNumberOfTasks").send_keys("3")
    # 64 | click | css=input:nth-child(11) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(11)").click()
    # 65 | type | id=id_11-SelectionAlgorithm.type | Sobol
    self.driver.find_element(By.ID, "id_11-SelectionAlgorithm.type").send_keys("Sobol")
    # 66 | click | css=input:nth-child(6) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(6)").click()
    # 67 | type | id=id_12-General.NumberOfWorkers | 3
    self.driver.find_element(By.ID, "id_12-General.NumberOfWorkers").send_keys("3")
    # 68 | type | id=id_12-General.result_storage | save
    self.driver.find_element(By.ID, "id_12-General.result_storage").send_keys("save")
    # 69 | click | css=input:nth-child(7) | 
    self.driver.find_element(By.CSS_SELECTOR, "input:nth-child(7)").click()
  
