include "wcel.mm"
include "cv.mm"
include "wtr.mm"
include "wsbc.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "idn1.mm"
include "wceq.mm"
include "biidd.mm"
include "sbcieg.mm"
include "e1a.mm"
include "sbcel2gv.mm"
include "imbi13.mm"
include "a1i.mm"
include "e1111.mm"
include "sbcim2g.mm"
include "bibi1.mm"
include "biimprcd.mm"
include "e11.mm"
include "pm3.31.mm"
include "pm3.3.mm"
include "impbii.mm"
include "biimprd.mm"
include "e10.mm"
include "ax-gen.mm"
include "sbcbi.mm"
include "bitr3.mm"
include "com12.mm"
include "gen11.mm"
include "albi.mm"
include "sbcalgOLD.mm"
include "dftr2.mm"
include "biantr.mm"
include "ex.mm"
include "in1.mm"

theorem trsbcVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  assert |- ( A e. B -> ( [. A / x ]. Tr x <-> Tr A ) )

  proof
    cA
    cB
    wcel
    #
    vx
    cv
    #
    wtr
    #
    vx
    cA
    wsbc
    #
    cA
    wtr
    #
    wb
    #
    @0
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    @7
    @1
    wcel
    #
    wa
    @6
    @1
    wcel
    #
    wi
    #
    vy
    wal
    #
    vz
    wal
    #
    vx
    cA
    wsbc
    #
    @4
    wb
    #
    @3
    @14
    wb
    #
    @5
    @0
    @14
    @8
    @7
    cA
    wcel
    #
    wa
    @6
    cA
    wcel
    #
    wi
    #
    vy
    wal
    #
    vz
    wal
    #
    wb
    #
    @4
    @21
    wb
    #
    @15
    @0
    @12
    vx
    cA
    wsbc
    #
    vz
    wal
    #
    @21
    wb
    #
    @14
    @25
    wb
    #
    @22
    @0
    @24
    @20
    wb
    #
    vz
    wal
    @26
    @0
    @28
    vz
    @0
    @11
    vx
    cA
    wsbc
    #
    vy
    wal
    #
    @20
    wb
    #
    @24
    @30
    wb
    #
    @28
    @0
    @29
    @19
    wb
    #
    vy
    wal
    @31
    @0
    @33
    vy
    @0
    @8
    @9
    @10
    wi
    wi
    #
    vx
    cA
    wsbc
    #
    @19
    wb
    #
    @35
    @29
    wb
    #
    @33
    @0
    @35
    @8
    @17
    @18
    wi
    wi
    #
    wb
    #
    @38
    @19
    wb
    #
    @36
    @0
    @8
    vx
    cA
    wsbc
    #
    @9
    vx
    cA
    wsbc
    #
    @10
    vx
    cA
    wsbc
    #
    wi
    wi
    #
    @38
    wb
    #
    @35
    @44
    wb
    #
    @39
    @0
    @0
    @41
    @8
    wb
    #
    @42
    @17
    wb
    #
    @43
    @18
    wb
    #
    @45
    @0
    idn1
    #
    @0
    @0
    @47
    @50
    @8
    @8
    vx
    cA
    cB
    @1
    cA
    wceq
    @8
    biidd
    sbcieg
    e1a
    @0
    @0
    @48
    @50
    vx
    @7
    cA
    cB
    sbcel2gv
    e1a
    @0
    @0
    @49
    @50
    vx
    @6
    cA
    cB
    sbcel2gv
    e1a
    @47
    @48
    @49
    @45
    wi
    wi
    wi
    @0
    @41
    @8
    @42
    @17
    @43
    @18
    imbi13
    a1i
    e1111
    @0
    @0
    @46
    @50
    @8
    @9
    @10
    vx
    cA
    cB
    sbcim2g
    e1a
    @46
    @39
    @45
    @35
    @44
    @38
    bibi1
    biimprcd
    e11
    @38
    @19
    @8
    @17
    @18
    pm3.31
    @8
    @17
    @18
    pm3.3
    impbii
    @39
    @36
    @40
    @35
    @38
    @19
    bibi1
    biimprd
    e10
    @0
    @0
    @34
    @11
    wb
    #
    vx
    wal
    @37
    @50
    @51
    vx
    @34
    @11
    @8
    @9
    @10
    pm3.31
    @8
    @9
    @10
    pm3.3
    impbii
    ax-gen
    @34
    @11
    vx
    cA
    cB
    sbcbi
    e10
    @37
    @36
    @33
    @35
    @29
    @19
    bitr3
    com12
    e11
    gen11
    @29
    @19
    vy
    albi
    e1a
    @0
    @0
    @32
    @50
    @11
    vy
    vx
    cA
    cB
    sbcalgOLD
    e1a
    @32
    @28
    @31
    @24
    @30
    @20
    bibi1
    biimprcd
    e11
    gen11
    @24
    @20
    vz
    albi
    e1a
    @0
    @0
    @27
    @50
    @12
    vz
    vx
    cA
    cB
    sbcalgOLD
    e1a
    @27
    @22
    @26
    @14
    @25
    @21
    bibi1
    biimprcd
    e11
    vz
    vy
    cA
    dftr2
    @22
    @23
    @15
    @14
    @21
    @4
    biantr
    ex
    e10
    @0
    @0
    @2
    @13
    wb
    #
    vx
    wal
    @16
    @50
    @52
    vx
    vz
    vy
    @1
    dftr2
    ax-gen
    @2
    @13
    vx
    cA
    cB
    sbcbi
    e10
    @16
    @5
    @15
    @3
    @14
    @4
    bibi1
    biimprcd
    e11
    in1
end
