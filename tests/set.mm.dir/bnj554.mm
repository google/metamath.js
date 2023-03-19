include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "cfv.mm"
include "wb.mm"
include "wcel.mm"
include "com.mm"
include "bnj1254.mm"
include "simp3bi.mm"
include "wa.mm"
include "simpr.mm"
include "bnj551.mm"
include "fveq2.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "iuneq1.mm"
include "3eqtr4g.mm"
include "syl.mm"
include "eqeqan12d.mm"
include "syl2anc.mm"
include "syl2an.mm"

theorem bnj554
  let wet: wff et
  let wze: wff ze
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cL: class L
  let vp: setvar p
  assume bnj554.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj554.20: |- ( ze <-> ( i e. _om /\ suc i e. n /\ m = suc i ) )
  assume bnj554.21: |- K = U_ y e. ( G ` i ) _pred ( y , A , R )
  assume bnj554.22: |- L = U_ y e. ( G ` p ) _pred ( y , A , R )
  assume bnj554.23: |- K = U_ y e. ( G ` i ) _pred ( y , A , R )
  assume bnj554.24: |- L = U_ y e. ( G ` p ) _pred ( y , A , R )

  disjoint G y
  disjoint i y
  disjoint p y
  assert |- ( ( et /\ ze ) -> ( ( G ` m ) = L <-> ( G ` suc i ) = K ) )

  proof
    wet
    vm
    cv
    #
    vp
    cv
    #
    csuc
    wceq
    #
    @0
    vi
    cv
    #
    csuc
    #
    wceq
    #
    @0
    cG
    cfv
    #
    cL
    wceq
    @4
    cG
    cfv
    #
    cK
    wceq
    wb
    #
    wze
    wet
    @0
    cD
    wcel
    vn
    cv
    #
    @0
    csuc
    wceq
    @1
    com
    wcel
    @2
    bnj554.19
    bnj1254
    wze
    @3
    com
    wcel
    @4
    @9
    wcel
    @5
    bnj554.20
    simp3bi
    @2
    @5
    wa
    @5
    @1
    @3
    wceq
    #
    @8
    @2
    @5
    simpr
    vi
    vm
    vp
    bnj551
    @5
    @10
    @6
    @7
    cL
    cK
    @0
    @4
    cG
    fveq2
    @10
    @1
    cG
    cfv
    #
    @3
    cG
    cfv
    #
    wceq
    #
    cL
    cK
    wceq
    @1
    @3
    cG
    fveq2
    @13
    vy
    @11
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    vy
    @12
    @14
    ciun
    cL
    cK
    vy
    @11
    @12
    @14
    iuneq1
    bnj554.24
    bnj554.23
    3eqtr4g
    syl
    eqeqan12d
    syl2anc
    syl2an
end
