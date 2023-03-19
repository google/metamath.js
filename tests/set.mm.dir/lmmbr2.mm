include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cbl.mm"
include "cres.mm"
include "wf.mm"
include "cuz.mm"
include "crn.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "w3a.mm"
include "cdm.mm"
include "clt.mm"
include "cz.mm"
include "lmmbr.mm"
include "wa.mm"
include "df-3an.mm"
include "cxmt.mm"
include "wb.mm"
include "cpw.mm"
include "wfn.mm"
include "uzf.mm"
include "ffn.mm"
include "wceq.mm"
include "reseq2.mm"
include "id.mm"
include "feq12d.mm"
include "rexrn.mm"
include "mp2b.mm"
include "wfun.mm"
include "cxp.mm"
include "wss.mm"
include "simp2l.mm"
include "cvv.mm"
include "elfvdm.mm"
include "3ad2ant1.mm"
include "cnex.mm"
include "elpmg.mm"
include "sylancl.mm"
include "mpbid.mm"
include "simpld.mm"
include "ffvresb.mm"
include "syl.mm"
include "cxr.mm"
include "rpxr.mm"
include "elbl.mm"
include "syl3an3.mm"
include "xmetsym.mm"
include "breq1d.mm"
include "3expa.mm"
include "pm5.32da.mm"
include "3adant3.mm"
include "bitrd.mm"
include "3adant2l.mm"
include "anbi2d.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "ralbidva.mm"

theorem lmmbr2
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vy: setvar y
  let cM: class M
  let cR: class R
  let cZ: class Z
  assume lmmbr.2: |- J = ( MetOpen ` D )
  assume lmmbr.3: |- ( ph -> D e. ( *Met ` X ) )

  disjoint j k
  disjoint j x
  disjoint D j
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint J x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint j u
  disjoint j y
  disjoint k u
  disjoint k y
  disjoint u x
  disjoint u y
  disjoint D u
  disjoint x y
  disjoint D y
  disjoint F u
  disjoint F y
  disjoint P u
  disjoint P y
  disjoint X u
  disjoint X y
  disjoint J u
  disjoint J y
  disjoint M j
  disjoint ph u
  disjoint R j
  disjoint R k
  disjoint R x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> ( F e. ( X ^pm CC ) /\ P e. X /\ A. x e. RR+ E. j e. ZZ A. k e. ( ZZ>= ` j ) ( k e. dom F /\ ( F ` k ) e. X /\ ( ( F ` k ) D P ) < x ) ) ) )

  proof
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    cP
    cX
    wcel
    #
    vy
    cv
    #
    cP
    vx
    cv
    #
    cD
    cbl
    cfv
    co
    #
    cF
    @2
    cres
    #
    wf
    #
    vy
    cuz
    crn
    wrex
    #
    vx
    crp
    wral
    #
    w3a
    #
    @0
    @1
    vk
    cv
    #
    cF
    cdm
    wcel
    #
    @10
    cF
    cfv
    #
    cX
    wcel
    #
    @12
    cP
    cD
    co
    #
    @3
    clt
    wbr
    #
    w3a
    #
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    w3a
    #
    wph
    vx
    vy
    cD
    cP
    cF
    cJ
    cX
    lmmbr.2
    lmmbr.3
    lmmbr
    wph
    @9
    @0
    @1
    wa
    #
    @20
    wa
    #
    @21
    @9
    @22
    @8
    wa
    #
    wph
    @23
    @0
    @1
    @8
    df-3an
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @24
    @23
    wb
    lmmbr.3
    @25
    @22
    @8
    @20
    @25
    @22
    wa
    @7
    @19
    vx
    crp
    @25
    @22
    @3
    crp
    wcel
    #
    @7
    @19
    wb
    @7
    @17
    @4
    cF
    @17
    cres
    #
    wf
    #
    vj
    cz
    wrex
    #
    @25
    @22
    @26
    w3a
    #
    @19
    cz
    cz
    cpw
    #
    cuz
    wf
    cuz
    cz
    wfn
    @7
    @29
    wb
    uzf
    cz
    @31
    cuz
    ffn
    @6
    @28
    vy
    vj
    cz
    cuz
    @2
    @17
    wceq
    #
    @2
    @17
    @4
    @5
    @27
    @2
    @17
    cF
    reseq2
    @32
    id
    feq12d
    rexrn
    mp2b
    @30
    @28
    @18
    vj
    cz
    @30
    @28
    @11
    @12
    @4
    wcel
    #
    wa
    #
    vk
    @17
    wral
    #
    @18
    @30
    cF
    wfun
    #
    @28
    @35
    wb
    @30
    @36
    cF
    cc
    cX
    cxp
    wss
    #
    @30
    @0
    @36
    @37
    wa
    #
    @25
    @0
    @1
    @26
    simp2l
    @30
    cX
    cxmt
    cdm
    #
    wcel
    #
    cc
    cvv
    wcel
    @0
    @38
    wb
    @25
    @22
    @40
    @26
    cD
    cX
    cxmt
    elfvdm
    3ad2ant1
    cnex
    cX
    cc
    cF
    @39
    cvv
    elpmg
    sylancl
    mpbid
    simpld
    vk
    @17
    @4
    cF
    ffvresb
    syl
    @30
    @34
    @16
    vk
    @17
    @30
    @34
    @11
    @13
    @15
    wa
    #
    wa
    @16
    @30
    @33
    @41
    @11
    @25
    @1
    @26
    @33
    @41
    wb
    @0
    @25
    @1
    @26
    w3a
    @33
    @13
    cP
    @12
    cD
    co
    #
    @3
    clt
    wbr
    #
    wa
    #
    @41
    @26
    @25
    @1
    @3
    cxr
    wcel
    @33
    @44
    wb
    @3
    rpxr
    @12
    cD
    cP
    @3
    cX
    elbl
    syl3an3
    @25
    @1
    @44
    @41
    wb
    @26
    @25
    @1
    wa
    @13
    @43
    @15
    @25
    @1
    @13
    @43
    @15
    wb
    @25
    @1
    @13
    w3a
    @42
    @14
    @3
    clt
    cP
    @12
    cD
    cX
    xmetsym
    breq1d
    3expa
    pm5.32da
    3adant3
    bitrd
    3adant2l
    anbi2d
    @11
    @13
    @15
    3anass
    syl6bbr
    ralbidv
    bitrd
    rexbidv
    syl5bb
    3expa
    ralbidva
    pm5.32da
    syl
    syl5bb
    @0
    @1
    @20
    df-3an
    syl6bbr
    bitrd
end
