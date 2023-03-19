include "cof.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "csn.mm"
include "c2nd.mm"
include "ciun.mm"
include "cdif.mm"
include "cun.mm"
include "ofpreima.mm"
include "wceq.mm"
include "inundif.mm"
include "iuneq1.mm"
include "ax-mp.mm"
include "iunxun.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "c0.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "simpr.mm"
include "eldifbd.mm"
include "cop.mm"
include "wi.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wfn.mm"
include "fndm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "1st2nd2.mm"
include "elxp6.mm"
include "simplbi2.mm"
include "3syl.mm"
include "mtod.mm"
include "ianor.mm"
include "sylib.mm"
include "disjsn.mm"
include "orbi12i.mm"
include "sylibr.mm"
include "wf.mm"
include "ffnd.mm"
include "dffn3.mm"
include "adantr.mm"
include "fimacnvdisj.mm"
include "ineq1.mm"
include "0in.mm"
include "ex.mm"
include "ineq2.mm"
include "in0.mm"
include "jaao.mm"
include "syl2an2r.mm"
include "mpd.mm"
include "iuneq2dv.mm"
include "iun0.mm"
include "uneq2d.mm"
include "un0.mm"
include "eqtrd.mm"

theorem ofpreima2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume ofpreima.1: |- ( ph -> F : A --> B )
  assume ofpreima.2: |- ( ph -> G : A --> C )
  assume ofpreima.3: |- ( ph -> A e. V )
  assume ofpreima.4: |- ( ph -> R Fn ( B X. C ) )

  disjoint A p
  disjoint D p
  disjoint F p
  disjoint G p
  disjoint R p
  disjoint p ph
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p y
  disjoint q s
  disjoint q x
  disjoint q y
  disjoint A q
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint C s
  disjoint C x
  disjoint C y
  disjoint D q
  disjoint F q
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint G q
  disjoint G s
  disjoint G x
  disjoint G y
  disjoint R q
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint ph q
  disjoint ph s
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( `' ( F oF R G ) " D ) = U_ p e. ( ( `' R " D ) i^i ( ran F X. ran G ) ) ( ( `' F " { ( 1st ` p ) } ) i^i ( `' G " { ( 2nd ` p ) } ) ) )

  proof
    wph
    cF
    cG
    cR
    cof
    co
    ccnv
    cD
    cima
    #
    vp
    cR
    ccnv
    cD
    cima
    #
    cF
    crn
    #
    cG
    crn
    #
    cxp
    #
    cin
    #
    cF
    ccnv
    vp
    cv
    #
    c1st
    cfv
    #
    csn
    #
    cima
    #
    cG
    ccnv
    @6
    c2nd
    cfv
    #
    csn
    #
    cima
    #
    cin
    #
    ciun
    #
    vp
    @1
    @4
    cdif
    #
    @13
    ciun
    #
    cun
    #
    @14
    wph
    @0
    vp
    @1
    @13
    ciun
    #
    @17
    wph
    cA
    cB
    cC
    cD
    cR
    cF
    cG
    cV
    vp
    ofpreima.1
    ofpreima.2
    ofpreima.3
    ofpreima.4
    ofpreima
    vp
    @5
    @15
    cun
    #
    @13
    ciun
    #
    @18
    @17
    @19
    @1
    wceq
    @20
    @18
    wceq
    @1
    @4
    inundif
    vp
    @19
    @1
    @13
    iuneq1
    ax-mp
    vp
    @5
    @15
    @13
    iunxun
    eqtr3i
    syl6eq
    wph
    @17
    @14
    c0
    cun
    @14
    wph
    @16
    c0
    @14
    wph
    @16
    vp
    @15
    c0
    ciun
    c0
    wph
    vp
    @15
    @13
    c0
    wph
    @6
    @15
    wcel
    #
    wa
    #
    @2
    @8
    cin
    c0
    wceq
    #
    @3
    @11
    cin
    c0
    wceq
    #
    wo
    #
    @13
    c0
    wceq
    #
    @22
    @7
    @2
    wcel
    #
    wn
    #
    @10
    @3
    wcel
    #
    wn
    #
    wo
    #
    @25
    @22
    @27
    @29
    wa
    #
    wn
    @31
    @22
    @32
    @6
    @4
    wcel
    #
    @22
    @6
    @1
    @4
    wph
    @21
    simpr
    eldifbd
    @22
    @6
    cB
    cC
    cxp
    #
    wcel
    @6
    @7
    @10
    cop
    wceq
    #
    @32
    @33
    wi
    wph
    @15
    @34
    @6
    wph
    @1
    @34
    @4
    wph
    cR
    cdm
    #
    @1
    @34
    cR
    cD
    cnvimass
    wph
    cR
    @34
    wfn
    @36
    @34
    wceq
    ofpreima.4
    @34
    cR
    fndm
    syl
    syl5sseq
    ssdifssd
    sselda
    @6
    cB
    cC
    1st2nd2
    @33
    @35
    @32
    @6
    @2
    @3
    elxp6
    simplbi2
    3syl
    mtod
    @27
    @29
    ianor
    sylib
    @23
    @28
    @24
    @30
    @2
    @7
    disjsn
    @3
    @10
    disjsn
    orbi12i
    sylibr
    wph
    cA
    @2
    cF
    wf
    #
    @21
    cA
    @3
    cG
    wf
    #
    @25
    @26
    wi
    wph
    cF
    cA
    wfn
    @37
    wph
    cA
    cB
    cF
    ofpreima.1
    ffnd
    cA
    cF
    dffn3
    sylib
    wph
    @38
    @21
    wph
    cG
    cA
    wfn
    @38
    wph
    cA
    cC
    cG
    ofpreima.2
    ffnd
    cA
    cG
    dffn3
    sylib
    adantr
    @37
    @23
    @26
    @38
    @24
    @37
    @23
    @26
    @37
    @23
    wa
    @9
    c0
    wceq
    #
    @26
    cA
    @2
    @8
    cF
    fimacnvdisj
    @39
    @13
    c0
    @12
    cin
    c0
    @9
    c0
    @12
    ineq1
    @12
    0in
    syl6eq
    syl
    ex
    @38
    @24
    @26
    @38
    @24
    wa
    @12
    c0
    wceq
    #
    @26
    cA
    @3
    @11
    cG
    fimacnvdisj
    @40
    @13
    @9
    c0
    cin
    c0
    @12
    c0
    @9
    ineq2
    @9
    in0
    syl6eq
    syl
    ex
    jaao
    syl2an2r
    mpd
    iuneq2dv
    vp
    @15
    iun0
    syl6eq
    uneq2d
    @14
    un0
    syl6eq
    eqtrd
end
