include "cz.mm"
include "cvv.mm"
include "wcel.mm"
include "cpr.mm"
include "cmap.mm"
include "co.mm"
include "zex.mm"
include "prex.mm"
include "wa.mm"
include "wf.mm"
include "c2.mm"
include "c3.mm"
include "cneg.mm"
include "wss.mm"
include "wne.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "c6.mm"
include "eqeltri.mm"
include "c4.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "2z.mm"
include "3nn0.mm"
include "nn0negzi.mm"
include "zlmodzxzldeplem.mm"
include "w3a.mm"
include "fprg.mm"
include "feq1i.mm"
include "sylibr.mm"
include "syl3anc.mm"
include "prssi.mm"
include "mp2an.mm"
include "fss.mm"
include "sylancl.mm"
include "elmapg.mm"
include "mpbird.mm"

theorem zlmodzxzldeplem1
  let cA: class A
  let cB: class B
  let cF: class F
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume zlmodzxzldep.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzldep.a: |- A = { <. 0 , 3 >. , <. 1 , 6 >. }
  assume zlmodzxzldep.b: |- B = { <. 0 , 2 >. , <. 1 , 4 >. }
  assume zlmodzxzldeplem.f: |- F = { <. A , 2 >. , <. B , -u 3 >. }


  assert |- F e. ( ZZ ^m { A , B } )

  proof
    cz
    cvv
    wcel
    #
    cA
    cB
    cpr
    #
    cvv
    wcel
    #
    cF
    cz
    @1
    cmap
    co
    wcel
    #
    zex
    cA
    cB
    prex
    @0
    @2
    wa
    #
    @3
    @1
    cz
    cF
    wf
    #
    @4
    @1
    c2
    c3
    cneg
    #
    cpr
    #
    cF
    wf
    #
    @7
    cz
    wss
    #
    @5
    @4
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    c2
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    wa
    #
    cA
    cB
    wne
    #
    @8
    @12
    @4
    @10
    @11
    cA
    cc0
    c3
    cop
    #
    c1
    c6
    cop
    #
    cpr
    cvv
    zlmodzxzldep.a
    @17
    @18
    prex
    eqeltri
    cB
    cc0
    c2
    cop
    #
    c1
    c4
    cop
    #
    cpr
    cvv
    zlmodzxzldep.b
    @19
    @20
    prex
    eqeltri
    pm3.2i
    a1i
    @15
    @4
    @13
    @14
    2z
    c3
    3nn0
    nn0negzi
    #
    pm3.2i
    a1i
    @16
    @4
    cA
    cB
    cZ
    zlmodzxzldep.z
    zlmodzxzldep.a
    zlmodzxzldep.b
    zlmodzxzldeplem
    a1i
    @12
    @15
    @16
    w3a
    @1
    @7
    cA
    c2
    cop
    cB
    @6
    cop
    cpr
    #
    wf
    @8
    cA
    cB
    c2
    @6
    cvv
    cvv
    cz
    cz
    fprg
    @1
    @7
    cF
    @22
    zlmodzxzldeplem.f
    feq1i
    sylibr
    syl3anc
    @13
    @14
    @9
    2z
    @21
    c2
    @6
    cz
    prssi
    mp2an
    @1
    @7
    cz
    cF
    fss
    sylancl
    cz
    @1
    cF
    cvv
    cvv
    elmapg
    mpbird
    mp2an
end
