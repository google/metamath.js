include "ssid.mm"
include "lecmii.mm"

theorem cmidi
  let cA: class A
  assume cmid.1: |- A e. CH


  assert |- A C_H A

  proof
    cA
    cA
    cmid.1
    cmid.1
    cA
    ssid
    lecmii
end
