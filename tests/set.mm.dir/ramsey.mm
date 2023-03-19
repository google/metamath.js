include "cn0.mm"
include "wcel.mm"
include "cfn.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "cmap.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "cram.mm"
include "ramcl.mm"
include "eqid.mm"
include "ramtcl2.mm"
include "mpbid.mm"
include "rabn0.mm"
include "sylib.mm"

theorem ramsey
  let vx: setvar x
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume ramsey.c: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )

  disjoint c f
  disjoint c n
  disjoint c s
  disjoint c x
  disjoint F c
  disjoint f n
  disjoint f s
  disjoint f x
  disjoint F f
  disjoint n s
  disjoint n x
  disjoint F n
  disjoint s x
  disjoint F s
  disjoint F x
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a i
  disjoint a n
  disjoint a s
  disjoint a x
  disjoint M a
  disjoint b c
  disjoint b f
  disjoint b i
  disjoint b n
  disjoint b s
  disjoint b x
  disjoint M b
  disjoint c i
  disjoint M c
  disjoint f i
  disjoint M f
  disjoint i n
  disjoint i s
  disjoint i x
  disjoint M i
  disjoint M n
  disjoint M s
  disjoint M x
  disjoint R c
  disjoint R f
  disjoint R n
  disjoint R s
  disjoint R x
  disjoint C c
  disjoint C f
  disjoint C x
  assert |- ( ( M e. NN0 /\ R e. Fin /\ F : R --> NN0 ) -> E. n e. NN0 A. s ( n <_ ( # ` s ) -> A. f e. ( R ^m ( s C M ) ) E. c e. R E. x e. ~P s ( ( F ` c ) <_ ( # ` x ) /\ ( x C M ) C_ ( `' f " { c } ) ) ) )

  proof
    cM
    cn0
    wcel
    cR
    cfn
    wcel
    cR
    cn0
    cF
    wf
    w3a
    #
    vn
    cv
    vs
    cv
    #
    chash
    cfv
    cle
    wbr
    vc
    cv
    #
    cF
    cfv
    vx
    cv
    #
    chash
    cfv
    cle
    wbr
    @3
    cM
    cC
    co
    vf
    cv
    ccnv
    @2
    csn
    cima
    wss
    wa
    vx
    @1
    cpw
    wrex
    vc
    cR
    wrex
    vf
    cR
    @1
    cM
    cC
    co
    cmap
    co
    wral
    wi
    vs
    wal
    #
    vn
    cn0
    crab
    #
    c0
    wne
    #
    @4
    vn
    cn0
    wrex
    @0
    cM
    cF
    cram
    co
    cn0
    wcel
    @6
    cR
    cF
    cM
    ramcl
    vx
    cC
    cR
    @5
    vf
    vi
    vn
    cF
    cM
    cfn
    vs
    va
    vb
    vc
    ramsey.c
    @5
    eqid
    ramtcl2
    mpbid
    @4
    vn
    cn0
    rabn0
    sylib
end
