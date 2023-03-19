include "c1o.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "weq.mm"
include "wn.mm"
include "wrex.mm"
include "cun.mm"
include "cxp.mm"
include "cdom.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "vex.mm"
include "1sdom.mm"
include "ax-mp.mm"
include "wa.mm"
include "reeanv.mm"
include "wel.mm"
include "w3a.mm"
include "wf1.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cif.mm"
include "cop.mm"
include "simpr.mm"
include "simp2r.mm"
include "simp1r.mm"
include "ifcld.mm"
include "ad2antrr.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "simp2l.mm"
include "simp1l.mm"
include "wo.mm"
include "elun.mm"
include "sylib.mm"
include "orcanai.mm"
include "ifclda.mm"
include "syl5eqel.mm"
include "fmptd.mm"
include "unxpdomlem1.mm"
include "ad2antrl.mm"
include "iftrue.mm"
include "adantr.mm"
include "sylan9eq.mm"
include "ad2antll.mm"
include "adantl.mm"
include "eqeq12d.mm"
include "ifex.mm"
include "opth1.mm"
include "syl6bi.mm"
include "simprr.mm"
include "simpll.mm"
include "simplr.mm"
include "unxpdomlem2.mm"
include "pm2.21d.mm"
include "eqcom.mm"
include "simprl.mm"
include "ancom2s.mm"
include "syl5bi.mm"
include "iffalse.mm"
include "opth.mm"
include "simprbi.mm"
include "4casesdan.mm"
include "ralrimivva.mm"
include "3ad2ant3.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "unex.mm"
include "xpex.mm"
include "f1dom2g.mm"
include "mp3an12.mm"
include "syl.mm"
include "3expia.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem unxpdomlem3
  let vx: setvar x
  let vt: setvar t
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z
  assume unxpdomlem1.1: |- F = ( x e. ( a u. b ) |-> G )
  assume unxpdomlem1.2: |- G = if ( x e. a , <. x , if ( x = m , t , s ) >. , <. if ( x = t , n , m ) , x >. )

  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m x
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint F w
  disjoint F z
  disjoint w z
  disjoint a w
  disjoint a z
  disjoint b w
  disjoint b z
  disjoint m w
  disjoint m z
  disjoint n w
  disjoint n z
  disjoint s w
  disjoint s z
  disjoint t w
  disjoint t z
  disjoint w x
  disjoint x z
  assert |- ( ( 1o ~< a /\ 1o ~< b ) -> ( a u. b ) ~<_ ( a X. b ) )

  proof
    c1o
    va
    cv
    #
    csdm
    wbr
    #
    vm
    vn
    weq
    wn
    #
    vn
    @0
    wrex
    #
    vm
    @0
    wrex
    #
    vs
    vt
    weq
    wn
    #
    vt
    vb
    cv
    #
    wrex
    #
    vs
    @6
    wrex
    #
    @0
    @6
    cun
    #
    @0
    @6
    cxp
    #
    cdom
    wbr
    #
    c1o
    @6
    csdm
    wbr
    #
    @0
    cvv
    wcel
    @1
    @4
    wb
    va
    vex
    #
    vm
    vn
    @0
    cvv
    1sdom
    ax-mp
    @6
    cvv
    wcel
    @12
    @8
    wb
    vb
    vex
    #
    vs
    vt
    @6
    cvv
    1sdom
    ax-mp
    @4
    @8
    wa
    @3
    @7
    wa
    #
    vs
    @6
    wrex
    vm
    @0
    wrex
    @11
    @3
    @7
    vm
    vs
    @0
    @6
    reeanv
    @15
    @11
    vm
    vs
    @0
    @6
    @15
    @2
    @5
    wa
    #
    vt
    @6
    wrex
    vn
    @0
    wrex
    vm
    va
    wel
    #
    vs
    vb
    wel
    #
    wa
    #
    @11
    @2
    @5
    vn
    vt
    @0
    @6
    reeanv
    @19
    @16
    @11
    vn
    vt
    @0
    @6
    @19
    vn
    va
    wel
    #
    vt
    vb
    wel
    #
    wa
    #
    @16
    @11
    @19
    @22
    @16
    w3a
    #
    @9
    @10
    cF
    wf1
    #
    @11
    @23
    @9
    @10
    cF
    wf
    vz
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vz
    vw
    weq
    #
    wi
    #
    vw
    @9
    wral
    vz
    @9
    wral
    #
    @24
    @23
    vx
    @9
    cG
    @10
    cF
    @23
    vx
    cv
    #
    @9
    wcel
    #
    wa
    #
    cG
    vx
    va
    wel
    #
    @33
    vx
    vm
    weq
    #
    vt
    cv
    #
    vs
    cv
    #
    cif
    #
    cop
    #
    vx
    vt
    weq
    #
    vn
    cv
    #
    vm
    cv
    #
    cif
    #
    @33
    cop
    #
    cif
    @10
    unxpdomlem1.2
    @35
    @36
    @41
    @46
    @10
    @35
    @36
    wa
    @36
    @40
    @6
    wcel
    #
    @41
    @10
    wcel
    @35
    @36
    simpr
    @23
    @47
    @34
    @36
    @23
    @37
    @38
    @39
    @6
    @19
    @20
    @21
    @16
    simp2r
    @17
    @18
    @22
    @16
    simp1r
    ifcld
    ad2antrr
    @33
    @40
    @0
    @6
    opelxpi
    syl2anc
    @35
    @36
    wn
    #
    wa
    @45
    @0
    wcel
    #
    vx
    vb
    wel
    #
    @46
    @10
    wcel
    @23
    @49
    @34
    @48
    @23
    @42
    @43
    @44
    @0
    @19
    @20
    @21
    @16
    simp2l
    @17
    @18
    @22
    @16
    simp1l
    ifcld
    ad2antrr
    @35
    @36
    @50
    @35
    @34
    @36
    @50
    wo
    @23
    @34
    simpr
    @33
    @0
    @6
    elun
    sylib
    orcanai
    @45
    @33
    @0
    @6
    opelxpi
    syl2anc
    ifclda
    syl5eqel
    unxpdomlem1.1
    fmptd
    @16
    @19
    @32
    @22
    @16
    @31
    vz
    vw
    @9
    @9
    @16
    @25
    @9
    wcel
    #
    @27
    @9
    wcel
    #
    wa
    #
    wa
    #
    vz
    va
    wel
    #
    vw
    va
    wel
    #
    @31
    @54
    @55
    @56
    wa
    #
    wa
    #
    @29
    @25
    vz
    vm
    weq
    #
    @38
    @39
    cif
    #
    cop
    #
    @27
    vw
    vm
    weq
    @38
    @39
    cif
    #
    cop
    #
    wceq
    @30
    @58
    @26
    @61
    @28
    @63
    @54
    @57
    @26
    @55
    @61
    vz
    vt
    weq
    #
    @43
    @44
    cif
    #
    @25
    cop
    #
    cif
    #
    @61
    @51
    @26
    @67
    wceq
    @16
    @52
    vx
    vz
    vt
    vm
    vn
    cF
    cG
    vs
    va
    vb
    unxpdomlem1.1
    unxpdomlem1.2
    unxpdomlem1
    ad2antrl
    #
    @55
    @67
    @61
    wceq
    @56
    @55
    @61
    @66
    iftrue
    adantr
    sylan9eq
    @54
    @57
    @28
    @56
    @63
    vw
    vt
    weq
    @43
    @44
    cif
    #
    @27
    cop
    #
    cif
    #
    @63
    @52
    @28
    @71
    wceq
    @16
    @51
    vx
    vw
    vt
    vm
    vn
    cF
    cG
    vs
    va
    vb
    unxpdomlem1.1
    unxpdomlem1.2
    unxpdomlem1
    ad2antll
    #
    @56
    @71
    @63
    wceq
    @55
    @56
    @63
    @70
    iftrue
    adantl
    sylan9eq
    eqeq12d
    @25
    @60
    @27
    @62
    vz
    vex
    #
    @59
    @38
    @39
    vt
    vex
    vs
    vex
    ifex
    opth1
    syl6bi
    @54
    @55
    @56
    wn
    #
    wa
    wa
    @29
    @30
    @54
    vx
    vz
    vw
    vt
    vm
    vn
    cF
    cG
    vs
    va
    vb
    unxpdomlem1.1
    unxpdomlem1.2
    @16
    @51
    @52
    simprr
    @2
    @5
    @53
    simpll
    #
    @2
    @5
    @53
    simplr
    #
    unxpdomlem2
    pm2.21d
    @29
    @28
    @26
    wceq
    #
    @54
    @55
    wn
    #
    @56
    wa
    wa
    #
    @30
    @26
    @28
    eqcom
    @79
    @77
    @30
    @54
    @56
    @78
    @77
    wn
    @54
    vx
    vw
    vz
    vt
    vm
    vn
    cF
    cG
    vs
    va
    vb
    unxpdomlem1.1
    unxpdomlem1.2
    @16
    @51
    @52
    simprl
    @75
    @76
    unxpdomlem2
    ancom2s
    pm2.21d
    syl5bi
    @54
    @78
    @74
    wa
    #
    wa
    #
    @29
    @66
    @70
    wceq
    #
    @30
    @81
    @26
    @66
    @28
    @70
    @54
    @80
    @26
    @67
    @66
    @68
    @78
    @67
    @66
    wceq
    @74
    @55
    @61
    @66
    iffalse
    adantr
    sylan9eq
    @54
    @80
    @28
    @71
    @70
    @72
    @74
    @71
    @70
    wceq
    @78
    @56
    @63
    @70
    iffalse
    adantl
    sylan9eq
    eqeq12d
    @82
    @65
    @69
    wceq
    @30
    @65
    @25
    @69
    @27
    @64
    @43
    @44
    vn
    vex
    vm
    vex
    ifex
    @73
    opth
    simprbi
    syl6bi
    4casesdan
    ralrimivva
    3ad2ant3
    vz
    vw
    @9
    @10
    cF
    dff13
    sylanbrc
    @9
    cvv
    wcel
    @10
    cvv
    wcel
    @24
    @11
    @0
    @6
    @13
    @14
    unex
    @0
    @6
    @13
    @14
    xpex
    @9
    @10
    cF
    cvv
    cvv
    f1dom2g
    mp3an12
    syl
    3expia
    rexlimdvva
    syl5bir
    rexlimivv
    sylbir
    syl2anb
end
