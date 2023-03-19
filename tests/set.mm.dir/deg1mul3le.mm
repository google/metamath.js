include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cco1.mm"
include "c0g.mm"
include "csupp.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wss.mm"
include "wbr.mm"
include "cn0.mm"
include "wf.mm"
include "ply1ring.mm"
include "3ad2ant1.mm"
include "ply1sclf.mm"
include "simp2.mm"
include "ffvelrnd.mm"
include "simp3.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "coe1f.mm"
include "syl.mm"
include "cv.mm"
include "cdif.mm"
include "wa.mm"
include "cmulr.mm"
include "wceq.mm"
include "eldifi.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "coe1sclmulfv.mm"
include "syl121anc.mm"
include "sylan2.mm"
include "cvv.mm"
include "3ad2ant3.mm"
include "ssid.mm"
include "a1i.mm"
include "nn0ex.mm"
include "fvexd.mm"
include "suppssr.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "3adant3.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "syl6ss.mm"
include "supxrss.mm"
include "syl2anc.mm"
include "deg1val.mm"
include "3brtr4d.mm"

theorem deg1mul3le
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let va: setvar a
  assume deg1mul3le.d: |- D = ( deg1 ` R )
  assume deg1mul3le.p: |- P = ( Poly1 ` R )
  assume deg1mul3le.k: |- K = ( Base ` R )
  assume deg1mul3le.b: |- B = ( Base ` P )
  assume deg1mul3le.t: |- .x. = ( .r ` P )
  assume deg1mul3le.a: |- A = ( algSc ` P )


  assert |- ( ( R e. Ring /\ F e. K /\ G e. B ) -> ( D ` ( ( A ` F ) .x. G ) ) <_ ( D ` G ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cK
    wcel
    #
    cG
    cB
    wcel
    #
    w3a
    #
    cF
    cA
    cfv
    #
    cG
    c.x
    co
    #
    cco1
    cfv
    #
    cR
    c0g
    cfv
    #
    csupp
    co
    #
    cxr
    clt
    csup
    #
    cG
    cco1
    cfv
    #
    @7
    csupp
    co
    #
    cxr
    clt
    csup
    #
    @5
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    cle
    @3
    @8
    @11
    wss
    @11
    cxr
    wss
    @9
    @12
    cle
    wbr
    @3
    cn0
    cK
    va
    @6
    @11
    @7
    @3
    @5
    cB
    wcel
    #
    cn0
    cK
    @6
    wf
    @3
    cP
    crg
    wcel
    #
    @4
    cB
    wcel
    @2
    @15
    @0
    @1
    @16
    @2
    cP
    cR
    deg1mul3le.p
    ply1ring
    3ad2ant1
    @3
    cK
    cB
    cF
    cA
    @0
    @1
    cK
    cB
    cA
    wf
    @2
    cA
    cB
    cP
    cR
    cK
    deg1mul3le.p
    deg1mul3le.a
    deg1mul3le.k
    deg1mul3le.b
    ply1sclf
    3ad2ant1
    @0
    @1
    @2
    simp2
    ffvelrnd
    @0
    @1
    @2
    simp3
    cB
    cP
    c.x
    @4
    cG
    deg1mul3le.b
    deg1mul3le.t
    ringcl
    syl3anc
    #
    @6
    cB
    cP
    cR
    @5
    cK
    @6
    eqid
    #
    deg1mul3le.b
    deg1mul3le.p
    deg1mul3le.k
    coe1f
    syl
    @3
    va
    cv
    #
    cn0
    @11
    cdif
    wcel
    #
    wa
    #
    @19
    @6
    cfv
    #
    cF
    @19
    @10
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    @7
    @24
    co
    #
    @7
    @20
    @3
    @19
    cn0
    wcel
    #
    @22
    @25
    wceq
    #
    @19
    cn0
    @11
    eldifi
    @3
    @27
    wa
    @0
    @1
    @2
    @27
    @28
    @0
    @1
    @2
    @27
    simpl1
    @0
    @1
    @2
    @27
    simpl2
    @0
    @1
    @2
    @27
    simpl3
    @3
    @27
    simpr
    cA
    cB
    cP
    cR
    c.x
    @24
    cK
    cF
    cG
    @19
    deg1mul3le.p
    deg1mul3le.b
    deg1mul3le.k
    deg1mul3le.a
    deg1mul3le.t
    @24
    eqid
    #
    coe1sclmulfv
    syl121anc
    sylan2
    @21
    @23
    @7
    cF
    @24
    @3
    cn0
    cK
    cvv
    @10
    cvv
    @11
    @19
    @7
    @2
    @0
    cn0
    cK
    @10
    wf
    #
    @1
    @10
    cB
    cP
    cR
    cG
    cK
    @10
    eqid
    #
    deg1mul3le.b
    deg1mul3le.p
    deg1mul3le.k
    coe1f
    3ad2ant3
    #
    @11
    @11
    wss
    @3
    @11
    ssid
    a1i
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    @3
    cR
    c0g
    fvexd
    suppssr
    oveq2d
    @3
    @26
    @7
    wceq
    #
    @20
    @0
    @1
    @33
    @2
    cK
    cR
    @24
    cF
    @7
    deg1mul3le.k
    @29
    @7
    eqid
    #
    ringrz
    3adant3
    adantr
    3eqtrd
    suppss
    @3
    @11
    cn0
    cxr
    @3
    @10
    cdm
    #
    @11
    cn0
    @10
    @7
    suppssdm
    @3
    @30
    @35
    cn0
    wceq
    @32
    cn0
    cK
    @10
    fdm
    syl
    syl5sseq
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    syl6ss
    @8
    @11
    supxrss
    syl2anc
    @3
    @15
    @13
    @9
    wceq
    @17
    @6
    cB
    cD
    cP
    cR
    @5
    @7
    deg1mul3le.d
    deg1mul3le.p
    deg1mul3le.b
    @34
    @18
    deg1val
    syl
    @2
    @0
    @14
    @12
    wceq
    @1
    @10
    cB
    cD
    cP
    cR
    cG
    @7
    deg1mul3le.d
    deg1mul3le.p
    deg1mul3le.b
    @34
    @31
    deg1val
    3ad2ant3
    3brtr4d
end
