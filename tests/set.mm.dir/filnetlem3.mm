include "cuni.mm"
include "wceq.mm"
include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "wss.mm"
include "cdir.mm"
include "wa.mm"
include "wi.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cid.mm"
include "cres.mm"
include "dmresi.mm"
include "filnetlem2.mm"
include "simpli.mm"
include "dmss.mm"
include "ax-mp.mm"
include "eqsstr3i.mm"
include "ssun1.mm"
include "sstri.mm"
include "dmrnssfld.mm"
include "simpri.mm"
include "uniss.mm"
include "mp2b.mm"
include "unixpss.mm"
include "unidm.mm"
include "sseqtri.mm"
include "eqssi.mm"
include "cv.mm"
include "csn.mm"
include "ciun.mm"
include "wral.mm"
include "filelss.mm"
include "xpss2.mm"
include "syl.mm"
include "ralrimiva.mm"
include "ss2iun.mm"
include "iunxpconst.mm"
include "syl6sseq.mm"
include "syl5eqss.mm"
include "wrel.mm"
include "ccom.mm"
include "ccnv.mm"
include "a1i.mm"
include "c1st.mm"
include "relopabi.mm"
include "jctil.mm"
include "wbr.mm"
include "wex.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "simpl.mm"
include "adantr.mm"
include "simprl.mm"
include "sseldd.mm"
include "xp1st.mm"
include "simprr.mm"
include "filinn0.mm"
include "syl3anc.mm"
include "n0.mm"
include "sylib.mm"
include "cop.mm"
include "filin.mm"
include "simpr.mm"
include "id.mm"
include "opeliunxp2.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "fvex.mm"
include "inex1.mm"
include "vex.mm"
include "op1st.mm"
include "inss1.mm"
include "eqsstri.mm"
include "opex.mm"
include "filnetlem1.mm"
include "mpbiran2.mm"
include "inss2.mm"
include "breq2.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "exlimddv.mm"
include "ralrimivva.mm"
include "codir.mm"
include "sylibr.mm"
include "wal.mm"
include "simplbi.mm"
include "simpld.mm"
include "simprd.mm"
include "anim12i.mm"
include "simprbi.mm"
include "sylan9ssr.mm"
include "ax-gen.mm"
include "gen2.mm"
include "cotr.mm"
include "mpbir.mm"
include "cvv.mm"
include "wb.mm"
include "filtop.mm"
include "xpexg.mm"
include "mpdan.mm"
include "ssexd.mm"
include "ssexg.mm"
include "sylancr.mm"
include "isdir.mm"
include "mpbir2and.mm"
include "jca.mm"
include "pm3.2i.mm"

theorem filnetlem3
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cX: class X
  let cA: class A
  let vd: setvar d
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  assume filnet.h: |- H = U_ n e. F ( { n } X. n )
  assume filnet.d: |- D = { <. x , y >. | ( ( x e. H /\ y e. H ) /\ ( 1st ` y ) C_ ( 1st ` x ) ) }

  disjoint x y
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint H x
  disjoint H y
  disjoint X n
  disjoint A x
  disjoint A y
  disjoint d f
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint H d
  disjoint H f
  disjoint H m
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H z
  disjoint B x
  disjoint B y
  disjoint D d
  disjoint D f
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint X d
  disjoint X f
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X z
  assert |- ( H = U. U. D /\ ( F e. ( Fil ` X ) -> ( H C_ ( F X. X ) /\ D e. DirRel ) ) )

  proof
    cH
    cD
    cuni
    #
    cuni
    #
    wceq
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cH
    cF
    cX
    cxp
    #
    wss
    #
    cD
    cdir
    wcel
    #
    wa
    wi
    cH
    @1
    cH
    cD
    cdm
    #
    cD
    crn
    #
    cun
    #
    @1
    cH
    @7
    @9
    cH
    cid
    cH
    cres
    #
    cdm
    #
    @7
    cH
    dmresi
    @10
    cD
    wss
    #
    @11
    @7
    wss
    @12
    cD
    cH
    cH
    cxp
    #
    wss
    #
    vx
    vy
    cD
    vn
    cF
    cH
    filnet.h
    filnet.d
    filnetlem2
    #
    simpli
    #
    @10
    cD
    dmss
    ax-mp
    eqsstr3i
    @7
    @8
    ssun1
    sstri
    cD
    dmrnssfld
    sstri
    @1
    @13
    cuni
    #
    cuni
    #
    cH
    @14
    @0
    @17
    wss
    @1
    @18
    wss
    @12
    @14
    @15
    simpri
    #
    cD
    @13
    uniss
    @0
    @17
    uniss
    mp2b
    @18
    cH
    cH
    cun
    cH
    cH
    cH
    unixpss
    cH
    unidm
    sseqtri
    sstri
    eqssi
    #
    @3
    @5
    @6
    @3
    cH
    vn
    cF
    vn
    cv
    #
    csn
    #
    @21
    cxp
    #
    ciun
    #
    @4
    filnet.h
    @3
    @24
    vn
    cF
    @22
    cX
    cxp
    #
    ciun
    #
    @4
    @3
    @23
    @25
    wss
    #
    vn
    cF
    wral
    @24
    @26
    wss
    @3
    @27
    vn
    cF
    @3
    @21
    cF
    wcel
    wa
    @21
    cX
    wss
    @27
    @21
    cF
    cX
    filelss
    @21
    cX
    @22
    xpss2
    syl
    ralrimiva
    vn
    cF
    @23
    @25
    ss2iun
    syl
    vn
    cF
    cX
    iunxpconst
    syl6sseq
    syl5eqss
    #
    @3
    @6
    cD
    wrel
    #
    @12
    wa
    #
    cD
    cD
    ccom
    cD
    wss
    #
    @13
    cD
    ccnv
    cD
    ccom
    wss
    #
    wa
    #
    @3
    @12
    @29
    @12
    @3
    @16
    a1i
    vx
    cv
    #
    cH
    wcel
    vy
    cv
    #
    cH
    wcel
    wa
    @35
    c1st
    cfv
    @34
    c1st
    cfv
    wss
    wa
    vx
    vy
    cD
    filnet.d
    relopabi
    jctil
    @3
    @32
    @31
    @3
    vv
    cv
    #
    vw
    cv
    #
    cD
    wbr
    #
    vz
    cv
    #
    @37
    cD
    wbr
    #
    wa
    #
    vw
    wex
    #
    vz
    cH
    wral
    vv
    cH
    wral
    @32
    @3
    @42
    vv
    vz
    cH
    cH
    @3
    @36
    cH
    wcel
    #
    @39
    cH
    wcel
    #
    wa
    #
    wa
    #
    vu
    cv
    #
    @36
    c1st
    cfv
    #
    @39
    c1st
    cfv
    #
    cin
    #
    wcel
    #
    @42
    vu
    @46
    @50
    c0
    wne
    #
    @51
    vu
    wex
    @46
    @3
    @48
    cF
    wcel
    #
    @49
    cF
    wcel
    #
    @52
    @3
    @45
    simpl
    #
    @46
    @36
    @4
    wcel
    @53
    @46
    cH
    @4
    @36
    @3
    @5
    @45
    @28
    adantr
    #
    @3
    @43
    @44
    simprl
    #
    sseldd
    @36
    cF
    cX
    xp1st
    syl
    #
    @46
    @39
    @4
    wcel
    @54
    @46
    cH
    @4
    @39
    @56
    @3
    @43
    @44
    simprr
    #
    sseldd
    @39
    cF
    cX
    xp1st
    syl
    #
    @48
    @49
    cF
    cX
    filinn0
    syl3anc
    vu
    @50
    n0
    sylib
    @46
    @51
    wa
    #
    @36
    @50
    @47
    cop
    #
    cD
    wbr
    #
    @39
    @62
    cD
    wbr
    #
    @42
    @61
    @43
    @62
    cH
    wcel
    #
    @63
    @46
    @43
    @51
    @57
    adantr
    @61
    @62
    @24
    cH
    @61
    @50
    cF
    wcel
    #
    @51
    @62
    @24
    wcel
    @46
    @66
    @51
    @46
    @3
    @53
    @54
    @66
    @55
    @58
    @60
    @48
    @49
    cF
    cX
    filin
    syl3anc
    adantr
    @46
    @51
    simpr
    vn
    cF
    @21
    @50
    @47
    @50
    @21
    @50
    wceq
    id
    opeliunxp2
    sylanbrc
    filnet.h
    syl6eleqr
    #
    @63
    @43
    @65
    wa
    @62
    c1st
    cfv
    #
    @48
    wss
    @68
    @50
    @48
    @50
    @47
    @48
    @49
    @36
    c1st
    fvex
    inex1
    vu
    vex
    op1st
    #
    @48
    @49
    inss1
    eqsstri
    vx
    vy
    @36
    @62
    cD
    vn
    cF
    cH
    filnet.h
    filnet.d
    vv
    vex
    #
    @50
    @47
    opex
    #
    filnetlem1
    mpbiran2
    sylanbrc
    @61
    @44
    @65
    @64
    @46
    @44
    @51
    @59
    adantr
    @67
    @64
    @44
    @65
    wa
    @68
    @49
    wss
    @68
    @50
    @49
    @69
    @48
    @49
    inss2
    eqsstri
    vx
    vy
    @39
    @62
    cD
    vn
    cF
    cH
    filnet.h
    filnet.d
    vz
    vex
    #
    @71
    filnetlem1
    mpbiran2
    sylanbrc
    @41
    @63
    @64
    wa
    vw
    @62
    @71
    @37
    @62
    wceq
    @38
    @63
    @40
    @64
    @37
    @62
    @36
    cD
    breq2
    @37
    @62
    @39
    cD
    breq2
    anbi12d
    spcev
    syl2anc
    exlimddv
    ralrimivva
    vv
    vz
    vw
    cH
    cH
    cD
    codir
    sylibr
    @31
    @38
    @37
    @39
    cD
    wbr
    #
    wa
    #
    @36
    @39
    cD
    wbr
    #
    wi
    #
    vz
    wal
    #
    vw
    wal
    vv
    wal
    @77
    vv
    vw
    @76
    vz
    @74
    @45
    @49
    @48
    wss
    @75
    @38
    @43
    @73
    @44
    @38
    @43
    @37
    cH
    wcel
    #
    @38
    @43
    @78
    wa
    #
    @37
    c1st
    cfv
    #
    @48
    wss
    #
    vx
    vy
    @36
    @37
    cD
    vn
    cF
    cH
    filnet.h
    filnet.d
    @70
    vw
    vex
    #
    filnetlem1
    #
    simplbi
    simpld
    @73
    @78
    @44
    @73
    @78
    @44
    wa
    #
    @49
    @80
    wss
    #
    vx
    vy
    @37
    @39
    cD
    vn
    cF
    cH
    filnet.h
    filnet.d
    @82
    @72
    filnetlem1
    #
    simplbi
    simprd
    anim12i
    @73
    @38
    @49
    @80
    @48
    @73
    @84
    @85
    @86
    simprbi
    @38
    @79
    @81
    @83
    simprbi
    sylan9ssr
    vx
    vy
    @36
    @39
    cD
    vn
    cF
    cH
    filnet.h
    filnet.d
    @70
    @72
    filnetlem1
    sylanbrc
    ax-gen
    gen2
    vv
    vw
    vz
    cD
    cotr
    mpbir
    jctil
    @3
    cD
    cvv
    wcel
    #
    @6
    @30
    @33
    wa
    wb
    @3
    @14
    @13
    cvv
    wcel
    #
    @87
    @19
    @3
    cH
    cvv
    wcel
    #
    @89
    @88
    @3
    cH
    @4
    cvv
    @3
    cX
    cF
    wcel
    @4
    cvv
    wcel
    cF
    cX
    filtop
    cF
    cX
    @2
    cF
    xpexg
    mpdan
    @28
    ssexd
    #
    @90
    cH
    cH
    cvv
    cvv
    xpexg
    syl2anc
    cD
    @13
    cvv
    ssexg
    sylancr
    cH
    cD
    cvv
    @20
    isdir
    syl
    mpbir2and
    jca
    pm3.2i
end
