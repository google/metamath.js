include "cfv.mm"
include "wceq.mm"
include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "eqcom.mm"
include "zring.mm"
include "csn.mm"
include "crsp.mm"
include "cqg.mm"
include "cec.mm"
include "eqid.mm"
include "znzrhval.mm"
include "3adant2.mm"
include "3adant3.mm"
include "eqeq12d.mm"
include "csubg.mm"
include "wer.mm"
include "crg.mm"
include "clidl.mm"
include "zringring.mm"
include "wss.mm"
include "nn0z.mm"
include "3ad2ant1.mm"
include "snssd.mm"
include "zringbas.mm"
include "rspcl.mm"
include "sylancr.mm"
include "lidlsubg.mm"
include "eqger.mm"
include "syl.mm"
include "simp3.mm"
include "erth.mm"
include "csg.mm"
include "cabl.mm"
include "wb.mm"
include "zringabl.mm"
include "lidlss.mm"
include "eqgabl.mm"
include "wa.mm"
include "simp2.mm"
include "jca.mm"
include "biantrurd.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "cv.mm"
include "cab.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "zsubrg.mm"
include "subrgsubg.mm"
include "mp1i.mm"
include "cnfldsub.mm"
include "df-zring.mm"
include "subgsub.mm"
include "syld3an1.mm"
include "eqcomd.mm"
include "dvdsrzring.mm"
include "rspsn.mm"
include "eleq12d.mm"
include "ovex.mm"
include "breq2.mm"
include "elab.mm"
include "syl6bb.mm"
include "3bitr2d.mm"
include "syl5bb.mm"

theorem zndvds
  let cA: class A
  let cB: class B
  let cL: class L
  let cN: class N
  let cY: class Y
  let vx: setvar x
  let vn: setvar n
  assume zncyg.y: |- Y = ( Z/nZ ` N )
  assume zndvds.2: |- L = ( ZRHom ` Y )


  assert |- ( ( N e. NN0 /\ A e. ZZ /\ B e. ZZ ) -> ( ( L ` A ) = ( L ` B ) <-> N || ( A - B ) ) )

  proof
    cA
    cL
    cfv
    #
    cB
    cL
    cfv
    #
    wceq
    @1
    @0
    wceq
    #
    cN
    cn0
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    w3a
    #
    cN
    cA
    cB
    cmin
    co
    #
    cdvds
    wbr
    #
    @0
    @1
    eqcom
    @6
    @2
    cB
    zring
    cN
    csn
    #
    zring
    crsp
    cfv
    #
    cfv
    #
    cqg
    co
    #
    cec
    #
    cA
    @12
    cec
    #
    wceq
    cB
    cA
    @12
    wbr
    #
    @8
    @6
    @1
    @13
    @0
    @14
    @3
    @5
    @1
    @13
    wceq
    @4
    cB
    @12
    @10
    cL
    cN
    cY
    @10
    eqid
    #
    @12
    eqid
    #
    zncyg.y
    zndvds.2
    znzrhval
    3adant2
    @3
    @4
    @0
    @14
    wceq
    @5
    cA
    @12
    @10
    cL
    cN
    cY
    @16
    @17
    zncyg.y
    zndvds.2
    znzrhval
    3adant3
    eqeq12d
    @6
    cB
    cA
    @12
    cz
    @6
    @11
    zring
    csubg
    cfv
    wcel
    #
    cz
    @12
    wer
    @6
    zring
    crg
    wcel
    #
    @11
    zring
    clidl
    cfv
    #
    wcel
    #
    @18
    zringring
    @6
    @19
    @9
    cz
    wss
    @21
    zringring
    @6
    cN
    cz
    @3
    @4
    cN
    cz
    wcel
    #
    @5
    cN
    nn0z
    3ad2ant1
    #
    snssd
    cz
    zring
    @20
    @9
    @10
    @16
    zringbas
    @20
    eqid
    #
    rspcl
    sylancr
    #
    zring
    @20
    @11
    @24
    lidlsubg
    sylancr
    @12
    zring
    cz
    @11
    zringbas
    @17
    eqger
    syl
    @3
    @4
    @5
    simp3
    #
    erth
    @6
    @15
    @5
    @4
    cA
    cB
    zring
    csg
    cfv
    #
    co
    #
    @11
    wcel
    #
    w3a
    #
    @29
    @8
    @6
    zring
    cabl
    wcel
    @11
    cz
    wss
    #
    @15
    @30
    wb
    zringabl
    @6
    @21
    @31
    @25
    cz
    @11
    @20
    zring
    zringbas
    @24
    lidlss
    syl
    cB
    cA
    @12
    @11
    zring
    @27
    cz
    zringbas
    @27
    eqid
    #
    @17
    eqgabl
    sylancr
    @6
    @29
    @5
    @4
    wa
    #
    @29
    wa
    @30
    @6
    @33
    @29
    @6
    @5
    @4
    @26
    @3
    @4
    @5
    simp2
    jca
    biantrurd
    @5
    @4
    @29
    df-3an
    syl6bbr
    @6
    @29
    @7
    cN
    vx
    cv
    #
    cdvds
    wbr
    #
    vx
    cab
    #
    wcel
    @8
    @6
    @28
    @7
    @11
    @36
    @6
    @7
    @28
    cz
    ccnfld
    csubg
    cfv
    wcel
    #
    @4
    @3
    @5
    @7
    @28
    wceq
    cz
    ccnfld
    csubrg
    cfv
    wcel
    @37
    @6
    zsubrg
    cz
    ccnfld
    subrgsubg
    mp1i
    cz
    ccnfld
    zring
    cmin
    @27
    cA
    cB
    cnfldsub
    df-zring
    @32
    subgsub
    syld3an1
    eqcomd
    @6
    @19
    @22
    @11
    @36
    wceq
    zringring
    @23
    vx
    cz
    cdvds
    zring
    cN
    @10
    zringbas
    @16
    dvdsrzring
    rspsn
    sylancr
    eleq12d
    @35
    @8
    vx
    @7
    cA
    cB
    cmin
    ovex
    @34
    @7
    cN
    cdvds
    breq2
    elab
    syl6bb
    3bitr2d
    3bitr2d
    syl5bb
end
