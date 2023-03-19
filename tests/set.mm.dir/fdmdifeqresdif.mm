include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "cres.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "eldifsn.mm"
include "neneq.mm"
include "simplbiim.mm"
include "adantl.mm"
include "iffalsed.mm"
include "mpteq2dva.mm"
include "reseq1i.mm"
include "difssd.mm"
include "resmptd.mm"
include "syl5eq.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn5.mm"
include "sylib.mm"
include "3eqtr4rd.mm"

theorem fdmdifeqresdif
  let vx: setvar x
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume fdmdifeqresdif.f: |- F = ( x e. D |-> if ( x = Y , X , ( G ` x ) ) )

  disjoint D x
  disjoint G x
  disjoint R x
  disjoint Y x
  disjoint k x
  assert |- ( G : ( D \ { Y } ) --> R -> G = ( F |` ( D \ { Y } ) ) )

  proof
    cD
    cY
    csn
    #
    cdif
    #
    cR
    cG
    wf
    #
    vx
    @1
    vx
    cv
    #
    cY
    wceq
    #
    cX
    @3
    cG
    cfv
    #
    cif
    #
    cmpt
    #
    vx
    @1
    @5
    cmpt
    #
    cF
    @1
    cres
    #
    cG
    @2
    vx
    @1
    @6
    @5
    @2
    @3
    @1
    wcel
    #
    wa
    @4
    cX
    @5
    @10
    @4
    wn
    #
    @2
    @10
    @3
    cD
    wcel
    @3
    cY
    wne
    @11
    @3
    cD
    cY
    eldifsn
    @3
    cY
    neneq
    simplbiim
    adantl
    iffalsed
    mpteq2dva
    @2
    @9
    vx
    cD
    @6
    cmpt
    #
    @1
    cres
    @7
    cF
    @12
    @1
    fdmdifeqresdif.f
    reseq1i
    @2
    vx
    cD
    @1
    @6
    @2
    cD
    @0
    difssd
    resmptd
    syl5eq
    @2
    cG
    @1
    wfn
    cG
    @8
    wceq
    @1
    cR
    cG
    ffn
    vx
    @1
    cG
    dffn5
    sylib
    3eqtr4rd
end
