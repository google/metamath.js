include "wcel.mm"
include "wss.mm"
include "wsbc.mm"
include "csb.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "idn1.mm"
include "sbcel2gOLD.mm"
include "e1a.mm"
include "imbi12.mm"
include "e11.mm"
include "sbcimg.mm"
include "bibi1.mm"
include "biimprcd.mm"
include "gen11.mm"
include "albi.mm"
include "sbcalgOLD.mm"
include "dfss2.mm"
include "ax-gen.mm"
include "sbcbi.mm"
include "e10.mm"
include "biantr.mm"
include "ex.mm"
include "in1.mm"

theorem sbcssgVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y


  assert |- ( A e. B -> ( [. A / x ]. C C_ D <-> [_ A / x ]_ C C_ [_ A / x ]_ D ) )

  proof
    cA
    cB
    wcel
    #
    cC
    cD
    wss
    #
    vx
    cA
    wsbc
    #
    vx
    cA
    cC
    csb
    #
    vx
    cA
    cD
    csb
    #
    wss
    #
    wb
    #
    @0
    @2
    vy
    cv
    #
    @3
    wcel
    #
    @7
    @4
    wcel
    #
    wi
    #
    vy
    wal
    #
    wb
    #
    @5
    @11
    wb
    #
    @6
    @0
    @7
    cC
    wcel
    #
    @7
    cD
    wcel
    #
    wi
    #
    vy
    wal
    #
    vx
    cA
    wsbc
    #
    @11
    wb
    #
    @2
    @18
    wb
    #
    @12
    @0
    @16
    vx
    cA
    wsbc
    #
    vy
    wal
    #
    @11
    wb
    #
    @18
    @22
    wb
    #
    @19
    @0
    @21
    @10
    wb
    #
    vy
    wal
    @23
    @0
    @25
    vy
    @0
    @14
    vx
    cA
    wsbc
    #
    @15
    vx
    cA
    wsbc
    #
    wi
    #
    @10
    wb
    #
    @21
    @28
    wb
    #
    @25
    @0
    @26
    @8
    wb
    #
    @27
    @9
    wb
    #
    @29
    @0
    @0
    @31
    @0
    idn1
    #
    vx
    cA
    @7
    cC
    cB
    sbcel2gOLD
    e1a
    @0
    @0
    @32
    @33
    vx
    cA
    @7
    cD
    cB
    sbcel2gOLD
    e1a
    @26
    @8
    @27
    @9
    imbi12
    e11
    @0
    @0
    @30
    @33
    @14
    @15
    vx
    cA
    cB
    sbcimg
    e1a
    @30
    @25
    @29
    @21
    @28
    @10
    bibi1
    biimprcd
    e11
    gen11
    @21
    @10
    vy
    albi
    e1a
    @0
    @0
    @24
    @33
    @16
    vy
    vx
    cA
    cB
    sbcalgOLD
    e1a
    @24
    @19
    @23
    @18
    @22
    @11
    bibi1
    biimprcd
    e11
    @0
    @0
    @1
    @17
    wb
    #
    vx
    wal
    @20
    @33
    @34
    vx
    vy
    cC
    cD
    dfss2
    ax-gen
    @1
    @17
    vx
    cA
    cB
    sbcbi
    e10
    @20
    @12
    @19
    @2
    @18
    @11
    bibi1
    biimprcd
    e11
    vy
    @3
    @4
    dfss2
    @12
    @13
    @6
    @2
    @11
    @5
    biantr
    ex
    e10
    in1
end
