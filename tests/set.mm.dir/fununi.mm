include "cv.mm"
include "wfun.mm"
include "wss.mm"
include "wo.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "wrel.mm"
include "cop.mm"
include "wcel.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "funrel.mm"
include "adantr.mm"
include "ralimi.mm"
include "reluni.mm"
include "sylibr.mm"
include "r19.28v.mm"
include "ssel.mm"
include "anim1d.mm"
include "dffun4.mm"
include "simprbi.mm"
include "19.21bbi.mm"
include "19.21bi.mm"
include "syl9r.mm"
include "adantl.mm"
include "anim2d.mm"
include "jaod.mm"
include "imp.mm"
include "2ralimi.mm"
include "funeq.mm"
include "sseq1.mm"
include "sseq2.mm"
include "orbi12d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "cbvral2v.mm"
include "ralcom.mm"
include "orcom.mm"
include "syl5bb.mm"
include "bitri.mm"
include "anbi12i.mm"
include "anidm.mm"
include "anandir.mm"
include "2ralbii.mm"
include "r19.26-2.mm"
include "bitr2i.mm"
include "3bitr3i.mm"
include "wex.mm"
include "eluni.mm"
include "eeanv.mm"
include "an4.mm"
include "ancom.mm"
include "2exbii.mm"
include "3bitr2i.mm"
include "imbi1i.mm"
include "19.23v.mm"
include "r2al.mm"
include "impexp.mm"
include "2albii.mm"
include "albii.mm"
include "3bitr2ri.mm"
include "3imtr4i.mm"
include "alrimiv.mm"
include "alrimivv.mm"
include "syl.mm"
include "sylanbrc.mm"

theorem fununi
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vw: setvar w

  disjoint f g
  disjoint A f
  disjoint A g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint f v
  disjoint f w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint g v
  disjoint g w
  disjoint x y
  disjoint x z
  disjoint v x
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint v y
  disjoint w y
  disjoint A y
  disjoint v z
  disjoint w z
  disjoint A z
  disjoint v w
  disjoint A v
  disjoint A w
  assert |- ( A. f e. A ( Fun f /\ A. g e. A ( f C_ g \/ g C_ f ) ) -> Fun U. A )

  proof
    vf
    cv
    #
    wfun
    #
    @0
    vg
    cv
    #
    wss
    #
    @2
    @0
    wss
    #
    wo
    #
    vg
    cA
    wral
    #
    wa
    #
    vf
    cA
    wral
    #
    cA
    cuni
    #
    wrel
    #
    vx
    cv
    #
    vy
    cv
    cop
    #
    @9
    wcel
    #
    @11
    vz
    cv
    cop
    #
    @9
    wcel
    #
    wa
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    @9
    wfun
    @8
    @0
    wrel
    #
    vf
    cA
    wral
    @10
    @7
    @21
    vf
    cA
    @1
    @21
    @6
    @0
    funrel
    adantr
    ralimi
    vf
    cA
    reluni
    sylibr
    @8
    @1
    @5
    wa
    #
    vg
    cA
    wral
    #
    vf
    cA
    wral
    #
    @20
    @7
    @23
    vf
    cA
    @1
    @5
    vg
    cA
    r19.28v
    ralimi
    @24
    @19
    vx
    vy
    @24
    @18
    vz
    vw
    cv
    #
    wfun
    #
    vv
    cv
    #
    wfun
    #
    wa
    #
    @25
    @27
    wss
    #
    @27
    @25
    wss
    #
    wo
    #
    wa
    #
    vv
    cA
    wral
    vw
    cA
    wral
    #
    @12
    @25
    wcel
    #
    @14
    @27
    wcel
    #
    wa
    #
    @17
    wi
    #
    vv
    cA
    wral
    vw
    cA
    wral
    #
    @24
    @18
    @33
    @38
    vw
    vv
    cA
    cA
    @29
    @32
    @38
    @29
    @30
    @38
    @31
    @28
    @30
    @38
    wi
    @26
    @30
    @37
    @12
    @27
    wcel
    #
    @36
    wa
    #
    @28
    @17
    @30
    @35
    @40
    @36
    @25
    @27
    @12
    ssel
    anim1d
    @28
    @41
    @17
    wi
    #
    vz
    @28
    @42
    vz
    wal
    #
    vx
    vy
    @28
    @27
    wrel
    @43
    vy
    wal
    vx
    wal
    vx
    vy
    vz
    @27
    dffun4
    simprbi
    19.21bbi
    19.21bi
    syl9r
    adantl
    @26
    @31
    @38
    wi
    @28
    @31
    @37
    @35
    @14
    @25
    wcel
    #
    wa
    #
    @26
    @17
    @31
    @36
    @44
    @35
    @27
    @25
    @14
    ssel
    anim2d
    @26
    @45
    @17
    wi
    #
    vz
    @26
    @46
    vz
    wal
    #
    vx
    vy
    @26
    @25
    wrel
    @47
    vy
    wal
    vx
    wal
    vx
    vy
    vz
    @25
    dffun4
    simprbi
    19.21bbi
    19.21bi
    syl9r
    adantr
    jaod
    imp
    2ralimi
    @24
    @24
    wa
    @26
    @32
    wa
    #
    vv
    cA
    wral
    vw
    cA
    wral
    #
    @28
    @32
    wa
    #
    vv
    cA
    wral
    vw
    cA
    wral
    #
    wa
    #
    @24
    @34
    @24
    @49
    @24
    @51
    @22
    @48
    @26
    @25
    @2
    wss
    #
    @2
    @25
    wss
    #
    wo
    #
    wa
    vf
    vg
    vw
    vv
    cA
    cA
    vf
    vw
    weq
    #
    @1
    @26
    @5
    @55
    @0
    @25
    funeq
    @56
    @3
    @53
    @4
    @54
    @0
    @25
    @2
    sseq1
    @0
    @25
    @2
    sseq2
    orbi12d
    anbi12d
    vg
    vv
    weq
    #
    @55
    @32
    @26
    @57
    @53
    @30
    @54
    @31
    @2
    @27
    @25
    sseq2
    @2
    @27
    @25
    sseq1
    orbi12d
    anbi2d
    cbvral2v
    @24
    @22
    vf
    cA
    wral
    vg
    cA
    wral
    @51
    @22
    vf
    vg
    cA
    cA
    ralcom
    @22
    @50
    @1
    @25
    @0
    wss
    #
    @0
    @25
    wss
    #
    wo
    #
    wa
    vg
    vf
    vw
    vv
    cA
    cA
    vg
    vw
    weq
    #
    @5
    @60
    @1
    @5
    @4
    @3
    wo
    @61
    @60
    @3
    @4
    orcom
    @61
    @4
    @58
    @3
    @59
    @2
    @25
    @0
    sseq1
    @2
    @25
    @0
    sseq2
    orbi12d
    syl5bb
    anbi2d
    vf
    vv
    weq
    #
    @1
    @28
    @60
    @32
    @0
    @27
    funeq
    @62
    @58
    @30
    @59
    @31
    @0
    @27
    @25
    sseq2
    @0
    @27
    @25
    sseq1
    orbi12d
    anbi12d
    cbvral2v
    bitri
    anbi12i
    @24
    anidm
    @34
    @48
    @50
    wa
    #
    vv
    cA
    wral
    vw
    cA
    wral
    @52
    @33
    @63
    vw
    vv
    cA
    cA
    @26
    @28
    @32
    anandir
    2ralbii
    @48
    @50
    vw
    vv
    cA
    cA
    r19.26-2
    bitr2i
    3bitr3i
    @18
    @25
    cA
    wcel
    #
    @27
    cA
    wcel
    #
    wa
    #
    @37
    wa
    #
    vv
    wex
    #
    vw
    wex
    #
    @17
    wi
    @68
    @17
    wi
    #
    vw
    wal
    #
    @39
    @16
    @69
    @17
    @16
    @35
    @64
    wa
    #
    vw
    wex
    #
    @36
    @65
    wa
    #
    vv
    wex
    #
    wa
    @72
    @74
    wa
    #
    vv
    wex
    vw
    wex
    @69
    @13
    @73
    @15
    @75
    vw
    @12
    cA
    eluni
    vv
    @14
    cA
    eluni
    anbi12i
    @72
    @74
    vw
    vv
    eeanv
    @76
    @67
    vw
    vv
    @76
    @37
    @66
    wa
    @67
    @35
    @64
    @36
    @65
    an4
    @37
    @66
    ancom
    bitri
    2exbii
    3bitr2i
    imbi1i
    @68
    @17
    vw
    19.23v
    @39
    @66
    @38
    wi
    #
    vv
    wal
    vw
    wal
    @67
    @17
    wi
    #
    vv
    wal
    #
    vw
    wal
    @71
    @38
    vw
    vv
    cA
    cA
    r2al
    @78
    @77
    vw
    vv
    @66
    @37
    @17
    impexp
    2albii
    @79
    @70
    vw
    @67
    @17
    vv
    19.23v
    albii
    3bitr2ri
    3bitr2i
    3imtr4i
    alrimiv
    alrimivv
    syl
    vx
    vy
    vz
    @9
    dffun4
    sylanbrc
end
