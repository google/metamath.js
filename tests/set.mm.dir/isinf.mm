include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "wss.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "com.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "wb.mm"
include "sseq1.mm"
include "adantl.mm"
include "breq1.mm"
include "sylan9bbr.mm"
include "anbi12d.mm"
include "cbvexdva.mm"
include "0ss.mm"
include "0ex.mm"
include "enref.mm"
include "spcev.mm"
include "mp2an.mm"
include "a1i.mm"
include "wi.mm"
include "w3a.mm"
include "cdif.mm"
include "ssdif0.mm"
include "eqss.mm"
include "wrex.mm"
include "biimpa.mm"
include "rspe.mm"
include "sylan2.mm"
include "isfi.mm"
include "sylibr.mm"
include "expcom.mm"
include "sylanbr.mm"
include "ex.mm"
include "sylan2br.mm"
include "3impd.mm"
include "com12.mm"
include "con3d.mm"
include "wf1o.mm"
include "bren.mm"
include "neq0.mm"
include "csn.mm"
include "cun.mm"
include "eldifi.mm"
include "snssd.mm"
include "unss.mm"
include "biimpi.mm"
include "ad2ant2r.mm"
include "cop.mm"
include "cin.mm"
include "vex.mm"
include "f1osn.mm"
include "jctr.mm"
include "eldifn.mm"
include "disjsn.mm"
include "word.mm"
include "nnord.mm"
include "orddisj.mm"
include "syl.mm"
include "anim12i.mm"
include "f1oun.mm"
include "syl2an.mm"
include "df-suc.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "snex.mm"
include "unex.mm"
include "f1oeq1.mm"
include "sylbir.mm"
include "adantll.mm"
include "syl2anc.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "com13.mm"
include "3imp.mm"
include "syld.mm"
include "3expia.mm"
include "com3l.mm"
include "finds2.mm"
include "ralrimiv.mm"

theorem isinf
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let vf: setvar f
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g

  disjoint A x
  disjoint A n
  disjoint n x
  disjoint A f
  disjoint A m
  disjoint A y
  disjoint A z
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint m n
  disjoint n y
  disjoint f g
  disjoint g m
  disjoint g x
  disjoint g y
  disjoint g z
  assert |- ( -. A e. Fin -> A. n e. _om E. x ( x C_ A /\ x ~~ n ) )

  proof
    cA
    cfn
    wcel
    #
    wn
    #
    vx
    cv
    #
    cA
    wss
    #
    @2
    vn
    cv
    #
    cen
    wbr
    #
    wa
    #
    vx
    wex
    #
    vn
    com
    @4
    com
    wcel
    @1
    @7
    @7
    @3
    @2
    c0
    cen
    wbr
    #
    wa
    #
    vx
    wex
    #
    @3
    @2
    vm
    cv
    #
    cen
    wbr
    #
    wa
    #
    vx
    wex
    #
    vy
    cv
    #
    cA
    wss
    #
    @15
    @11
    csuc
    #
    cen
    wbr
    #
    wa
    #
    vy
    wex
    #
    @1
    vn
    vm
    @4
    c0
    wceq
    #
    @6
    @9
    vx
    @21
    @5
    @8
    @3
    @4
    c0
    @2
    cen
    breq2
    anbi2d
    exbidv
    @4
    @11
    wceq
    #
    @6
    @13
    vx
    @22
    @5
    @12
    @3
    @4
    @11
    @2
    cen
    breq2
    anbi2d
    exbidv
    @4
    @17
    wceq
    #
    @6
    @19
    vx
    vy
    @23
    @2
    @15
    wceq
    #
    wa
    @3
    @16
    @5
    @18
    @24
    @3
    @16
    wb
    @23
    @2
    @15
    cA
    sseq1
    adantl
    @24
    @5
    @15
    @4
    cen
    wbr
    @23
    @18
    @2
    @15
    @4
    cen
    breq1
    @4
    @17
    @15
    cen
    breq2
    sylan9bbr
    anbi12d
    cbvexdva
    @10
    @1
    c0
    cA
    wss
    #
    c0
    c0
    cen
    wbr
    #
    @10
    cA
    0ss
    c0
    0ex
    enref
    @9
    @25
    @26
    wa
    vx
    c0
    0ex
    @2
    c0
    wceq
    @3
    @25
    @8
    @26
    @2
    c0
    cA
    sseq1
    @2
    c0
    c0
    cen
    breq1
    anbi12d
    spcev
    mp2an
    a1i
    @14
    @11
    com
    wcel
    #
    @1
    @20
    @13
    @27
    @1
    @20
    wi
    #
    wi
    vx
    @3
    @12
    @27
    @28
    @3
    @12
    @27
    w3a
    #
    @1
    cA
    @2
    cdif
    #
    c0
    wceq
    #
    wn
    #
    @20
    @29
    @31
    @0
    @31
    @29
    @0
    @31
    @3
    @12
    @27
    @0
    @3
    @31
    @12
    @27
    @0
    wi
    #
    wi
    #
    @31
    @3
    cA
    @2
    wss
    #
    @34
    cA
    @2
    ssdif0
    @3
    @35
    wa
    #
    @12
    @33
    @36
    @2
    cA
    wceq
    #
    @12
    @33
    @2
    cA
    eqss
    @27
    @37
    @12
    wa
    #
    @0
    @27
    @38
    wa
    cA
    @11
    cen
    wbr
    #
    vm
    com
    wrex
    #
    @0
    @38
    @27
    @39
    @40
    @37
    @12
    @39
    @2
    cA
    @11
    cen
    breq1
    biimpa
    @39
    vm
    com
    rspe
    sylan2
    vm
    cA
    isfi
    sylibr
    expcom
    sylanbr
    ex
    sylan2br
    expcom
    3impd
    com12
    con3d
    @3
    @12
    @27
    @32
    @20
    wi
    #
    @12
    @3
    @27
    @41
    wi
    #
    @12
    @2
    @11
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @3
    @42
    wi
    #
    @2
    @11
    vf
    bren
    @44
    @45
    vf
    @3
    @44
    @42
    @32
    @27
    @3
    @44
    wa
    #
    @20
    @32
    vz
    cv
    #
    @30
    wcel
    #
    vz
    wex
    @27
    @46
    @20
    wi
    #
    wi
    #
    vz
    @30
    neq0
    @48
    @50
    vz
    @48
    @27
    @49
    @46
    @48
    @27
    wa
    #
    @20
    @46
    @51
    wa
    @2
    @47
    csn
    #
    cun
    #
    cA
    wss
    #
    @53
    @17
    cen
    wbr
    #
    @20
    @3
    @48
    @54
    @44
    @27
    @48
    @3
    @52
    cA
    wss
    #
    @54
    @48
    @47
    cA
    @47
    cA
    @2
    eldifi
    snssd
    @3
    @56
    wa
    @54
    @2
    @52
    cA
    unss
    biimpi
    sylan2
    ad2ant2r
    @44
    @51
    @55
    @3
    @44
    @51
    wa
    @53
    @11
    @11
    csn
    #
    cun
    #
    @43
    @47
    @11
    cop
    #
    csn
    #
    cun
    #
    wf1o
    #
    @55
    @44
    @44
    @52
    @57
    @60
    wf1o
    #
    wa
    @2
    @52
    cin
    c0
    wceq
    #
    @11
    @57
    cin
    c0
    wceq
    #
    wa
    @62
    @51
    @44
    @63
    @47
    @11
    vz
    vex
    vm
    vex
    f1osn
    jctr
    @48
    @64
    @27
    @65
    @48
    @47
    @2
    wcel
    wn
    @64
    @47
    cA
    @2
    eldifn
    @2
    @47
    disjsn
    sylibr
    @27
    @11
    word
    @65
    @11
    nnord
    @11
    orddisj
    syl
    anim12i
    @2
    @11
    @52
    @57
    @43
    @60
    f1oun
    syl2an
    @62
    @53
    @17
    @61
    wf1o
    #
    @55
    @17
    @58
    wceq
    @66
    @62
    wb
    @11
    df-suc
    @17
    @58
    @53
    @61
    f1oeq3
    ax-mp
    @66
    @53
    @17
    vg
    cv
    #
    wf1o
    #
    vg
    wex
    @55
    @68
    @66
    vg
    @61
    @43
    @60
    vf
    vex
    @59
    snex
    unex
    @53
    @17
    @67
    @61
    f1oeq1
    spcev
    @53
    @17
    vg
    bren
    sylibr
    sylbir
    syl
    adantll
    @19
    @54
    @55
    wa
    vy
    @53
    @2
    @52
    vx
    vex
    @47
    snex
    unex
    @15
    @53
    wceq
    @16
    @54
    @18
    @55
    @15
    @53
    cA
    sseq1
    @15
    @53
    @17
    cen
    breq1
    anbi12d
    spcev
    syl2anc
    expcom
    ex
    exlimiv
    sylbi
    com13
    expcom
    exlimiv
    sylbi
    com12
    3imp
    syld
    3expia
    exlimiv
    com3l
    finds2
    com12
    ralrimiv
end
