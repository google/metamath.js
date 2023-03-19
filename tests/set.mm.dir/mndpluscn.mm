include "cv.mm"
include "ccnv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "ffn.mm"
include "fnov.mm"
include "biimpi.mm"
include "mp2b.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "wf1o.mm"
include "chmeo.mm"
include "toponunii.mm"
include "hmeof1o.mm"
include "ax-mp.mm"
include "f1ocnvdm.mm"
include "mpan.mm"
include "anim12i.mm"
include "rgen2a.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2va.mm"
include "sylancl.mm"
include "f1ocnvfv2.mm"
include "oveqan12d.mm"
include "eqtr2d.mm"
include "mpt2eq3ia.mm"
include "eqtri.mm"
include "wtru.mm"
include "ctopon.mm"
include "a1i.mm"
include "cnmpt1st.mm"
include "hmeocnvcn.mm"
include "mp1i.mm"
include "cnmpt21f.mm"
include "cnmpt2nd.mm"
include "cnmpt22f.mm"
include "hmeocn.mm"
include "trud.mm"
include "eqeltri.mm"

theorem mndpluscn
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let cF: class F
  let c.as: class .*
  let cJ: class J
  let cK: class K
  let va: setvar a
  let vb: setvar b
  assume mndpluscn.f: |- F e. ( J Homeo K )
  assume mndpluscn.p: |- .+ : ( B X. B ) --> B
  assume mndpluscn.t: |- .* : ( C X. C ) --> C
  assume mndpluscn.j: |- J e. ( TopOn ` B )
  assume mndpluscn.k: |- K e. ( TopOn ` C )
  assume mndpluscn.h: |- ( ( x e. B /\ y e. B ) -> ( F ` ( x .+ y ) ) = ( ( F ` x ) .* ( F ` y ) ) )
  assume mndpluscn.o: |- .+ e. ( ( J tX J ) Cn J )

  disjoint .* y
  disjoint x y
  disjoint .* x
  disjoint .+ y
  disjoint F y
  disjoint .+ x
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint a b
  disjoint a y
  disjoint .* a
  disjoint b y
  disjoint .* b
  disjoint a x
  disjoint .+ a
  disjoint .+ b
  disjoint C a
  disjoint C b
  disjoint F a
  disjoint F b
  disjoint J a
  disjoint J b
  disjoint K a
  disjoint K b
  assert |- .* e. ( ( K tX K ) Cn K )

  proof
    c.as
    va
    vb
    cC
    cC
    va
    cv
    #
    cF
    ccnv
    #
    cfv
    #
    vb
    cv
    #
    @1
    cfv
    #
    c.pl
    co
    #
    cF
    cfv
    #
    cmpt2
    #
    cK
    cK
    ctx
    co
    cK
    ccn
    co
    #
    c.as
    va
    vb
    cC
    cC
    @0
    @3
    c.as
    co
    #
    cmpt2
    #
    @7
    cC
    cC
    cxp
    #
    cC
    c.as
    wf
    c.as
    @11
    wfn
    #
    c.as
    @10
    wceq
    #
    mndpluscn.t
    @11
    cC
    c.as
    ffn
    @12
    @13
    va
    vb
    cC
    cC
    c.as
    fnov
    biimpi
    mp2b
    va
    vb
    cC
    cC
    @9
    @6
    @0
    cC
    wcel
    #
    @3
    cC
    wcel
    #
    wa
    #
    @6
    @2
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    c.as
    co
    #
    @9
    @16
    @2
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cF
    cfv
    #
    @22
    cF
    cfv
    #
    @23
    cF
    cfv
    #
    c.as
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @6
    @19
    wceq
    #
    @14
    @20
    @15
    @21
    cB
    cC
    cF
    wf1o
    #
    @14
    @20
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    @31
    mndpluscn.f
    cF
    cJ
    cK
    cB
    cC
    cB
    cJ
    mndpluscn.j
    toponunii
    cC
    cK
    mndpluscn.k
    toponunii
    hmeof1o
    ax-mp
    #
    cB
    cC
    @0
    cF
    f1ocnvdm
    mpan
    @31
    @15
    @21
    @33
    cB
    cC
    @3
    cF
    f1ocnvdm
    mpan
    anim12i
    @29
    vx
    vy
    cB
    mndpluscn.h
    rgen2a
    @29
    @30
    @2
    @23
    c.pl
    co
    #
    cF
    cfv
    #
    @17
    @27
    c.as
    co
    #
    wceq
    vx
    vy
    @2
    @4
    cB
    cB
    @22
    @2
    wceq
    #
    @25
    @35
    @28
    @36
    @37
    @24
    @34
    cF
    @22
    @2
    @23
    c.pl
    oveq1
    fveq2d
    @37
    @26
    @17
    @27
    c.as
    @22
    @2
    cF
    fveq2
    oveq1d
    eqeq12d
    @23
    @4
    wceq
    #
    @35
    @6
    @36
    @19
    @38
    @34
    @5
    cF
    @23
    @4
    @2
    c.pl
    oveq2
    fveq2d
    @38
    @27
    @18
    @17
    c.as
    @23
    @4
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2va
    sylancl
    @14
    @15
    @17
    @0
    @18
    @3
    c.as
    @31
    @14
    @17
    @0
    wceq
    @33
    cB
    cC
    @0
    cF
    f1ocnvfv2
    mpan
    @31
    @15
    @18
    @3
    wceq
    @33
    cB
    cC
    @3
    cF
    f1ocnvfv2
    mpan
    oveqan12d
    eqtr2d
    mpt2eq3ia
    eqtri
    @7
    @8
    wcel
    wtru
    va
    vb
    @5
    cF
    cK
    cK
    cJ
    cK
    cC
    cC
    cK
    cC
    ctopon
    cfv
    wcel
    wtru
    mndpluscn.k
    a1i
    #
    @39
    wtru
    va
    vb
    @2
    @4
    c.pl
    cK
    cK
    cJ
    cJ
    cJ
    cC
    cC
    @39
    @39
    wtru
    va
    vb
    @0
    @1
    cK
    cK
    cK
    cJ
    cC
    cC
    @39
    @39
    wtru
    va
    vb
    cK
    cK
    cC
    cC
    @39
    @39
    cnmpt1st
    @32
    @1
    cK
    cJ
    ccn
    co
    wcel
    wtru
    mndpluscn.f
    cF
    cJ
    cK
    hmeocnvcn
    mp1i
    #
    cnmpt21f
    wtru
    va
    vb
    @3
    @1
    cK
    cK
    cK
    cJ
    cC
    cC
    @39
    @39
    wtru
    va
    vb
    cK
    cK
    cC
    cC
    @39
    @39
    cnmpt2nd
    @40
    cnmpt21f
    c.pl
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    wtru
    mndpluscn.o
    a1i
    cnmpt22f
    @32
    cF
    cJ
    cK
    ccn
    co
    wcel
    wtru
    mndpluscn.f
    cF
    cJ
    cK
    hmeocn
    mp1i
    cnmpt21f
    trud
    eqeltri
end
