include "crtcl.mm"
include "cn0.mm"
include "dfrtrcl3.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "brmptiunrelexpd.mm"

theorem brfvrtrcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume brfvrtrcld.r: |- ( ph -> R e. _V )

  disjoint A n
  disjoint B n
  disjoint R n
  disjoint n r
  disjoint R r
  assert |- ( ph -> ( A ( t* ` R ) B <-> E. n e. NN0 A ( R ^r n ) B ) )

  proof
    wph
    cA
    cB
    crtcl
    cR
    vn
    cn0
    vr
    vn
    vr
    dfrtrcl3
    brfvrtrcld.r
    cn0
    cn0
    wss
    wph
    cn0
    ssid
    a1i
    brmptiunrelexpd
end
