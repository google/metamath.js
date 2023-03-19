include "cdomn.mm"
include "wcel.mm"
include "cmnd.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cn0.mm"
include "cres.mm"
include "wf.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "cc0.mm"
include "w3a.mm"
include "cmhm.mm"
include "cmgp.mm"
include "csubmnd.mm"
include "ply1domn.mm"
include "crg.mm"
include "eqid.mm"
include "isdomn3.mm"
include "simprbi.mm"
include "syl.mm"
include "submmnd.mm"
include "ccnfld.mm"
include "nn0subm.mm"
include "mp1i.mm"
include "jca.mm"
include "wfn.mm"
include "wss.mm"
include "cxr.mm"
include "deg1xrf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "difss.mm"
include "fnssres.mm"
include "mp2an.mm"
include "a1i.mm"
include "fvres.mm"
include "adantl.mm"
include "wne.mm"
include "domnring.mm"
include "adantr.mm"
include "eldifi.mm"
include "eldifsni.mm"
include "deg1nn0cl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "crlreg.mm"
include "ad2antrl.mm"
include "cco1.mm"
include "simpl.mm"
include "deg1ldgdomn.mm"
include "ad2antll.mm"
include "deg1mul2.mm"
include "ringcl.mm"
include "domnmuln0.mm"
include "syl122anc.mm"
include "eldifsn.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "cur.mm"
include "ringidcl.mm"
include "cnzr.mm"
include "domnnzr.mm"
include "nzrnz.mm"
include "3syl.mm"
include "ringidval.mm"
include "subm0.mm"
include "fveq2d.mm"
include "cmn1.mm"
include "mon1pid.mm"
include "simprd.mm"
include "3eqtr3d.mm"
include "3jca.mm"
include "cbs.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "cc.mm"
include "nn0sscn.mm"
include "cnfldbas.mm"
include "cvv.mm"
include "cplusg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "nn0ex.mm"
include "cnfldadd.mm"
include "cnfld0.mm"
include "ismhm.mm"

theorem deg1mhm
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cN: class N
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume deg1mhm.d: |- D = ( deg1 ` R )
  assume deg1mhm.b: |- B = ( Base ` P )
  assume deg1mhm.p: |- P = ( Poly1 ` R )
  assume deg1mhm.z: |- .0. = ( 0g ` P )
  assume deg1mhm.y: |- Y = ( ( mulGrp ` P ) |`s ( B \ { .0. } ) )
  assume deg1mhm.n: |- N = ( CCfld |`s NN0 )


  assert |- ( R e. Domn -> ( D |` ( B \ { .0. } ) ) e. ( Y MndHom N ) )

  proof
    cR
    cdomn
    wcel
    #
    cY
    cmnd
    wcel
    #
    cN
    cmnd
    wcel
    #
    wa
    cB
    c.0
    csn
    #
    cdif
    #
    cn0
    cD
    @4
    cres
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cP
    cmulr
    cfv
    #
    co
    #
    @5
    cfv
    #
    @7
    @5
    cfv
    #
    @8
    @5
    cfv
    #
    caddc
    co
    #
    wceq
    #
    vy
    @4
    wral
    vx
    @4
    wral
    #
    cY
    c0g
    cfv
    #
    @5
    cfv
    #
    cc0
    wceq
    #
    w3a
    @5
    cY
    cN
    cmhm
    co
    wcel
    @0
    @1
    @2
    @0
    @4
    cP
    cmgp
    cfv
    #
    csubmnd
    cfv
    wcel
    #
    @1
    @0
    cP
    cdomn
    wcel
    #
    @21
    cP
    cR
    deg1mhm.p
    ply1domn
    #
    @22
    cP
    crg
    wcel
    #
    @21
    cB
    cP
    @20
    c.0
    deg1mhm.b
    deg1mhm.z
    @20
    eqid
    #
    isdomn3
    simprbi
    syl
    #
    @4
    cY
    @20
    deg1mhm.y
    submmnd
    syl
    cn0
    ccnfld
    csubmnd
    cfv
    wcel
    #
    @2
    @0
    nn0subm
    cn0
    cN
    ccnfld
    deg1mhm.n
    submmnd
    mp1i
    jca
    @0
    @6
    @16
    @19
    @0
    @5
    @4
    wfn
    #
    @12
    cn0
    wcel
    #
    vx
    @4
    wral
    @6
    @28
    @0
    cD
    cB
    wfn
    #
    @4
    cB
    wss
    #
    @28
    cB
    cxr
    cD
    wf
    @30
    cB
    cD
    cP
    cR
    deg1mhm.d
    deg1mhm.p
    deg1mhm.b
    deg1xrf
    cB
    cxr
    cD
    ffn
    ax-mp
    cB
    @3
    difss
    #
    cB
    @4
    cD
    fnssres
    mp2an
    a1i
    @0
    @29
    vx
    @4
    @0
    @7
    @4
    wcel
    #
    wa
    #
    @12
    @7
    cD
    cfv
    #
    cn0
    @33
    @12
    @35
    wceq
    @0
    @7
    @4
    cD
    fvres
    #
    adantl
    @34
    cR
    crg
    wcel
    #
    @7
    cB
    wcel
    #
    @7
    c.0
    wne
    #
    @35
    cn0
    wcel
    @0
    @37
    @33
    cR
    domnring
    #
    adantr
    @33
    @38
    @0
    @7
    cB
    @3
    eldifi
    #
    adantl
    @33
    @39
    @0
    @7
    cB
    c.0
    eldifsni
    #
    adantl
    cB
    cD
    cP
    cR
    @7
    c.0
    deg1mhm.d
    deg1mhm.p
    deg1mhm.z
    deg1mhm.b
    deg1nn0cl
    syl3anc
    eqeltrd
    ralrimiva
    vx
    @4
    cn0
    @5
    ffnfv
    sylanbrc
    @0
    @15
    vx
    vy
    @4
    @4
    @0
    @33
    @8
    @4
    wcel
    #
    wa
    #
    wa
    #
    @10
    cD
    cfv
    #
    @35
    @8
    cD
    cfv
    #
    caddc
    co
    #
    @11
    @14
    @45
    cB
    cD
    cP
    cR
    @9
    cR
    crlreg
    cfv
    #
    @7
    @8
    c.0
    deg1mhm.d
    deg1mhm.p
    @49
    eqid
    #
    deg1mhm.b
    @9
    eqid
    #
    deg1mhm.z
    @0
    @37
    @44
    @40
    adantr
    @33
    @38
    @0
    @43
    @41
    ad2antrl
    #
    @33
    @39
    @0
    @43
    @42
    ad2antrl
    #
    @45
    @0
    @38
    @39
    @35
    @7
    cco1
    cfv
    #
    cfv
    @49
    wcel
    @0
    @44
    simpl
    @52
    @53
    @54
    cB
    cD
    cP
    cR
    @49
    @7
    c.0
    deg1mhm.d
    deg1mhm.p
    deg1mhm.z
    deg1mhm.b
    @50
    @54
    eqid
    deg1ldgdomn
    syl3anc
    @43
    @8
    cB
    wcel
    #
    @0
    @33
    @8
    cB
    @3
    eldifi
    ad2antll
    #
    @43
    @8
    c.0
    wne
    #
    @0
    @33
    @8
    cB
    c.0
    eldifsni
    ad2antll
    #
    deg1mul2
    @45
    @10
    @4
    wcel
    #
    @11
    @46
    wceq
    @45
    @10
    cB
    wcel
    #
    @10
    c.0
    wne
    #
    @59
    @45
    @24
    @38
    @55
    @60
    @0
    @24
    @44
    @0
    @22
    @24
    @23
    cP
    domnring
    syl
    #
    adantr
    @52
    @56
    cB
    cP
    @9
    @7
    @8
    deg1mhm.b
    @51
    ringcl
    syl3anc
    @45
    @22
    @38
    @39
    @55
    @57
    @61
    @0
    @22
    @44
    @23
    adantr
    @52
    @53
    @56
    @58
    cB
    cP
    @9
    @7
    @8
    c.0
    deg1mhm.b
    @51
    deg1mhm.z
    domnmuln0
    syl122anc
    @10
    cB
    c.0
    eldifsn
    sylanbrc
    @10
    @4
    cD
    fvres
    syl
    @44
    @14
    @48
    wceq
    @0
    @33
    @43
    @12
    @35
    @13
    @47
    caddc
    @36
    @8
    @4
    cD
    fvres
    oveqan12d
    adantl
    3eqtr4d
    ralrimivva
    @0
    cP
    cur
    cfv
    #
    @5
    cfv
    #
    @63
    cD
    cfv
    #
    @18
    cc0
    @0
    @63
    @4
    wcel
    #
    @64
    @65
    wceq
    @0
    @63
    cB
    wcel
    #
    @63
    c.0
    wne
    #
    @66
    @0
    @24
    @67
    @62
    cB
    cP
    @63
    deg1mhm.b
    @63
    eqid
    #
    ringidcl
    syl
    @0
    @22
    cP
    cnzr
    wcel
    @68
    @23
    cP
    domnnzr
    cP
    @63
    c.0
    @69
    deg1mhm.z
    nzrnz
    3syl
    @63
    cB
    c.0
    eldifsn
    sylanbrc
    @63
    @4
    cD
    fvres
    syl
    @0
    @63
    @17
    @5
    @0
    @21
    @63
    @17
    wceq
    @26
    @4
    cY
    @20
    @63
    deg1mhm.y
    cP
    @63
    @20
    @25
    @69
    ringidval
    subm0
    syl
    fveq2d
    @0
    cR
    cnzr
    wcel
    #
    @65
    cc0
    wceq
    #
    cR
    domnnzr
    @70
    @63
    cR
    cmn1
    cfv
    #
    wcel
    @71
    cD
    cP
    cR
    @63
    @72
    deg1mhm.p
    @69
    @72
    eqid
    deg1mhm.d
    mon1pid
    simprd
    syl
    3eqtr3d
    3jca
    vx
    vy
    @4
    cn0
    @9
    caddc
    cY
    cN
    @5
    cc0
    @17
    @31
    @4
    cY
    cbs
    cfv
    wceq
    @32
    @4
    cB
    cY
    @20
    deg1mhm.y
    cB
    cP
    @20
    @25
    deg1mhm.b
    mgpbas
    ressbas2
    ax-mp
    cn0
    cc
    wss
    cn0
    cN
    cbs
    cfv
    wceq
    nn0sscn
    cn0
    cc
    cN
    ccnfld
    deg1mhm.n
    cnfldbas
    ressbas2
    ax-mp
    @4
    cvv
    wcel
    #
    @9
    cY
    cplusg
    cfv
    wceq
    cB
    cvv
    wcel
    @73
    cB
    cP
    cbs
    cfv
    cvv
    deg1mhm.b
    cP
    cbs
    fvex
    eqeltri
    cB
    @3
    cvv
    difexg
    ax-mp
    @4
    @9
    @20
    cY
    cvv
    deg1mhm.y
    cP
    @9
    @20
    @25
    @51
    mgpplusg
    ressplusg
    ax-mp
    cn0
    cvv
    wcel
    caddc
    cN
    cplusg
    cfv
    wceq
    nn0ex
    cn0
    caddc
    ccnfld
    cN
    cvv
    deg1mhm.n
    cnfldadd
    ressplusg
    ax-mp
    @17
    eqid
    @27
    cc0
    cN
    c0g
    cfv
    wceq
    nn0subm
    cn0
    cN
    ccnfld
    cc0
    deg1mhm.n
    cnfld0
    subm0
    ax-mp
    ismhm
    sylanbrc
end
