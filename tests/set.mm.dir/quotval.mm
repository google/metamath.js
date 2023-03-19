include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "c0p.mm"
include "wne.mm"
include "cquot.mm"
include "co.mm"
include "wceq.mm"
include "cdgr.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "crio.mm"
include "plyssc.mm"
include "sseli.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "cv.mm"
include "cmul.mm"
include "cof.mm"
include "cmin.mm"
include "wsbc.mm"
include "oveq1.mm"
include "oveq12.mm"
include "sylan2.mm"
include "syl6eqr.mm"
include "sbceq1d.mm"
include "cvv.mm"
include "ovex.mm"
include "eqeltri.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "orbi12d.mm"
include "sbcie.mm"
include "simpr.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "orbi2d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "riotabidv.mm"
include "df-quot.mm"
include "riotaex.mm"
include "ovmpt2a.mm"
include "sylan2br.mm"
include "3impb.mm"
include "syl3an2.mm"
include "syl3an1.mm"

theorem quotval
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vq: setvar q
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  assume quotval.1: |- R = ( F oF - ( G oF x. q ) )

  disjoint F q
  disjoint G q
  disjoint f g
  disjoint f q
  disjoint f r
  disjoint F f
  disjoint g q
  disjoint g r
  disjoint F g
  disjoint q r
  disjoint F r
  disjoint G f
  disjoint G g
  disjoint R f
  disjoint R g
  disjoint R r
  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) /\ G =/= 0p ) -> ( F quot G ) = ( iota_ q e. ( Poly ` CC ) ( R = 0p \/ ( deg ` R ) < ( deg ` G ) ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    cF
    cc
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    cG
    c0p
    wne
    #
    cF
    cG
    cquot
    co
    cR
    c0p
    wceq
    #
    cR
    cdgr
    cfv
    #
    cG
    cdgr
    cfv
    #
    clt
    wbr
    #
    wo
    #
    vq
    @1
    crio
    #
    wceq
    #
    @0
    @1
    cF
    cS
    plyssc
    #
    sseli
    @3
    @2
    cG
    @1
    wcel
    #
    @4
    @11
    @0
    @1
    cG
    @12
    sseli
    @2
    @13
    @4
    @11
    @13
    @4
    wa
    @2
    cG
    @1
    c0p
    csn
    cdif
    #
    wcel
    @11
    cG
    @1
    c0p
    eldifsn
    vf
    vg
    cF
    cG
    @1
    @14
    vr
    cv
    #
    c0p
    wceq
    #
    @15
    cdgr
    cfv
    #
    vg
    cv
    #
    cdgr
    cfv
    #
    clt
    wbr
    #
    wo
    #
    vr
    vf
    cv
    #
    @18
    vq
    cv
    #
    cmul
    cof
    #
    co
    #
    cmin
    cof
    #
    co
    #
    wsbc
    #
    vq
    @1
    crio
    @10
    cquot
    @22
    cF
    wceq
    #
    @18
    cG
    wceq
    #
    wa
    #
    @28
    @9
    vq
    @1
    @31
    @28
    @21
    vr
    cR
    wsbc
    #
    @9
    @31
    @21
    vr
    @27
    cR
    @31
    @27
    cF
    cG
    @23
    @24
    co
    #
    @26
    co
    #
    cR
    @30
    @29
    @25
    @33
    wceq
    @27
    @34
    wceq
    @18
    cG
    @23
    @24
    oveq1
    @22
    cF
    @25
    @33
    @26
    oveq12
    sylan2
    quotval.1
    syl6eqr
    sbceq1d
    @32
    @5
    @6
    @19
    clt
    wbr
    #
    wo
    #
    @31
    @9
    @21
    @36
    vr
    cR
    cR
    @34
    cvv
    quotval.1
    cF
    @33
    @26
    ovex
    eqeltri
    @15
    cR
    wceq
    #
    @16
    @5
    @20
    @35
    @15
    cR
    c0p
    eqeq1
    @37
    @17
    @6
    @19
    clt
    @15
    cR
    cdgr
    fveq2
    breq1d
    orbi12d
    sbcie
    @31
    @35
    @8
    @5
    @31
    @19
    @7
    @6
    clt
    @31
    @18
    cG
    cdgr
    @29
    @30
    simpr
    fveq2d
    breq2d
    orbi2d
    syl5bb
    bitrd
    riotabidv
    vf
    vg
    vr
    vq
    df-quot
    @9
    vq
    @1
    riotaex
    ovmpt2a
    sylan2br
    3impb
    syl3an2
    syl3an1
end
