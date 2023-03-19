include "clmod.mm"
include "wcel.mm"
include "zring.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "crg.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cvv.mm"
include "zringring.mm"
include "prex.mm"
include "frlmlmod.mm"
include "mp2an.mm"
include "frlmsca.mm"
include "pm3.2i.mm"

theorem zlmodzxzlmod
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume zlmodzxz.z: |- Z = ( ZZring freeLMod { 0 , 1 } )


  assert |- ( Z e. LMod /\ ZZring = ( Scalar ` Z ) )

  proof
    cZ
    clmod
    wcel
    #
    zring
    cZ
    csca
    cfv
    wceq
    #
    zring
    crg
    wcel
    #
    cc0
    c1
    cpr
    #
    cvv
    wcel
    #
    @0
    zringring
    cc0
    c1
    prex
    #
    zring
    cZ
    @3
    cvv
    zlmodzxz.z
    frlmlmod
    mp2an
    @2
    @4
    @1
    zringring
    @5
    zring
    cZ
    @3
    crg
    cvv
    zlmodzxz.z
    frlmsca
    mp2an
    pm3.2i
end
