include "cn0.mm"
include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "cuz.mm"
include "cfv.mm"
include "cdif.mm"
include "cv.mm"
include "wf1.mm"
include "cres.mm"
include "cid.mm"
include "wceq.mm"
include "wex.mm"
include "simplr.mm"
include "fzfi.mm"
include "difinf.mm"
include "sylancl.mm"
include "diffi.mm"
include "ax-mp.mm"
include "isinffi.mm"
include "cun.mm"
include "crn.mm"
include "wf1o.mm"
include "cin.mm"
include "c0.mm"
include "f1f1orn.mm"
include "adantl.mm"
include "f1oi.mm"
include "a1i.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "syl.mm"
include "ssrin.mm"
include "syl6sseq.mm"
include "ss0.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "f1of1.mm"
include "wb.mm"
include "uncom.mm"
include "simplrr.mm"
include "fzss2.mm"
include "undif.mm"
include "sylib.mm"
include "syl5eq.mm"
include "f1eq2.mm"
include "mpbid.mm"
include "difss2d.mm"
include "simplrl.mm"
include "unssd.mm"
include "f1ss.mm"
include "syl2anc.mm"
include "resundir.mm"
include "cdm.mm"
include "dmres.mm"
include "f1dm.mm"
include "ineq1d.mm"
include "syl6eq.mm"
include "wrel.mm"
include "relres.mm"
include "reldm0.mm"
include "sylibr.mm"
include "residm.mm"
include "uneq12d.mm"
include "un0.mm"
include "vex.mm"
include "cvv.mm"
include "ovex.mm"
include "resiexg.mm"
include "unex.mm"
include "f1eq1.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "spcev.mm"
include "exlimddv.mm"

theorem eldioph2lem2
  let cA: class A
  let cS: class S
  let cN: class N
  let vc: setvar c
  let va: setvar a

  disjoint N c
  disjoint S c
  disjoint A c
  disjoint N a
  disjoint a c
  disjoint S a
  disjoint A a
  assert |- ( ( ( N e. NN0 /\ -. S e. Fin ) /\ ( ( 1 ... N ) C_ S /\ A e. ( ZZ>= ` N ) ) ) -> E. c ( c : ( 1 ... A ) -1-1-> S /\ ( c |` ( 1 ... N ) ) = ( _I |` ( 1 ... N ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cS
    cfn
    wcel
    wn
    #
    wa
    #
    c1
    cN
    cfz
    co
    #
    cS
    wss
    #
    cA
    cN
    cuz
    cfv
    wcel
    #
    wa
    #
    wa
    #
    c1
    cA
    cfz
    co
    #
    @3
    cdif
    #
    cS
    @3
    cdif
    #
    va
    cv
    #
    wf1
    #
    @8
    cS
    vc
    cv
    #
    wf1
    #
    @13
    @3
    cres
    #
    cid
    @3
    cres
    #
    wceq
    #
    wa
    #
    vc
    wex
    #
    va
    @7
    @10
    cfn
    wcel
    wn
    #
    @9
    cfn
    wcel
    #
    @12
    va
    wex
    @7
    @1
    @3
    cfn
    wcel
    @20
    @0
    @1
    @6
    simplr
    c1
    cN
    fzfi
    cS
    @3
    difinf
    sylancl
    @8
    cfn
    wcel
    @21
    c1
    cA
    fzfi
    @8
    @3
    diffi
    ax-mp
    @10
    @9
    va
    isinffi
    sylancl
    @7
    @12
    wa
    #
    @8
    cS
    @11
    @16
    cun
    #
    wf1
    #
    @23
    @3
    cres
    #
    @16
    wceq
    #
    @19
    @22
    @8
    @11
    crn
    #
    @3
    cun
    #
    @23
    wf1
    #
    @28
    cS
    wss
    @24
    @22
    @9
    @3
    cun
    #
    @28
    @23
    wf1
    #
    @29
    @22
    @30
    @28
    @23
    wf1o
    #
    @31
    @22
    @9
    @27
    @11
    wf1o
    #
    @3
    @3
    @16
    wf1o
    #
    @9
    @3
    cin
    #
    c0
    wceq
    #
    @27
    @3
    cin
    #
    c0
    wceq
    #
    @32
    @12
    @33
    @7
    @9
    @10
    @11
    f1f1orn
    adantl
    @34
    @22
    @3
    f1oi
    a1i
    @36
    @22
    @35
    @3
    @9
    cin
    c0
    @9
    @3
    incom
    @3
    @8
    disjdif
    eqtri
    #
    a1i
    @22
    @37
    c0
    wss
    @38
    @22
    @37
    @10
    @3
    cin
    #
    c0
    @22
    @27
    @10
    wss
    #
    @37
    @40
    wss
    @12
    @41
    @7
    @12
    @9
    @10
    @11
    wf
    @41
    @9
    @10
    @11
    f1f
    @9
    @10
    @11
    frn
    syl
    #
    adantl
    @27
    @10
    @3
    ssrin
    syl
    @40
    @3
    @10
    cin
    c0
    @10
    @3
    incom
    @3
    cS
    disjdif
    eqtri
    syl6sseq
    @37
    ss0
    syl
    @9
    @27
    @3
    @3
    @11
    @16
    f1oun
    syl22anc
    @30
    @28
    @23
    f1of1
    syl
    @22
    @30
    @8
    wceq
    @31
    @29
    wb
    @22
    @30
    @3
    @9
    cun
    #
    @8
    @9
    @3
    uncom
    @22
    @3
    @8
    wss
    #
    @43
    @8
    wceq
    @22
    @5
    @44
    @2
    @4
    @5
    @12
    simplrr
    cN
    c1
    cA
    fzss2
    syl
    @3
    @8
    undif
    sylib
    syl5eq
    @30
    @8
    @28
    @23
    f1eq2
    syl
    mpbid
    @22
    @27
    @3
    cS
    @12
    @27
    cS
    wss
    @7
    @12
    @27
    cS
    @3
    @42
    difss2d
    adantl
    @2
    @4
    @5
    @12
    simplrl
    unssd
    @8
    @28
    cS
    @23
    f1ss
    syl2anc
    @22
    @25
    @11
    @3
    cres
    #
    @16
    @3
    cres
    #
    cun
    #
    @16
    @11
    @16
    @3
    resundir
    @22
    @47
    c0
    @16
    cun
    #
    @16
    @22
    @45
    c0
    @46
    @16
    @22
    @45
    cdm
    #
    c0
    wceq
    #
    @45
    c0
    wceq
    #
    @22
    @49
    @3
    @11
    cdm
    #
    cin
    #
    c0
    @11
    @3
    dmres
    @22
    @53
    @52
    @3
    cin
    #
    c0
    @3
    @52
    incom
    @22
    @54
    @35
    c0
    @22
    @52
    @9
    @3
    @12
    @52
    @9
    wceq
    @7
    @9
    @10
    @11
    f1dm
    adantl
    ineq1d
    @39
    syl6eq
    syl5eq
    syl5eq
    @45
    wrel
    @51
    @50
    wb
    @11
    @3
    relres
    @45
    reldm0
    ax-mp
    sylibr
    @46
    @16
    wceq
    @22
    cid
    @3
    residm
    a1i
    uneq12d
    @48
    @16
    c0
    cun
    @16
    c0
    @16
    uncom
    @16
    un0
    eqtri
    syl6eq
    syl5eq
    @18
    @24
    @26
    wa
    vc
    @23
    @11
    @16
    va
    vex
    @3
    cvv
    wcel
    @16
    cvv
    wcel
    c1
    cN
    cfz
    ovex
    @3
    cvv
    resiexg
    ax-mp
    unex
    @13
    @23
    wceq
    #
    @14
    @24
    @17
    @26
    @8
    cS
    @13
    @23
    f1eq1
    @55
    @15
    @25
    @16
    @13
    @23
    @3
    reseq1
    eqeq1d
    anbi12d
    spcev
    syl2anc
    exlimddv
end
