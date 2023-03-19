include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "nfcv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "nfiu1.mm"
include "nfcxfr.mm"
include "nfop.mm"
include "nfsn.mm"
include "nfun.mm"
include "nffv.mm"
include "nfeq1.mm"
include "nf5ri.mm"

theorem bnj958
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  assume bnj958.1: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj958.2: |- G = ( f u. { <. n , C >. } )

  disjoint f y
  disjoint i y
  disjoint n y
  assert |- ( ( G ` i ) = ( f ` i ) -> A. y ( G ` i ) = ( f ` i ) )

  proof
    vi
    cv
    #
    cG
    cfv
    #
    @0
    vf
    cv
    #
    cfv
    #
    wceq
    vy
    vy
    @1
    @3
    vy
    @0
    cG
    vy
    cG
    @2
    vn
    cv
    #
    cC
    cop
    #
    csn
    #
    cun
    bnj958.2
    vy
    @2
    @6
    vy
    @2
    nfcv
    vy
    @5
    vy
    @4
    cC
    vy
    @4
    nfcv
    vy
    cC
    vy
    vm
    cv
    @2
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    bnj958.1
    vy
    @7
    @8
    nfiu1
    nfcxfr
    nfop
    nfsn
    nfun
    nfcxfr
    vy
    @0
    nfcv
    nffv
    nfeq1
    nf5ri
end
