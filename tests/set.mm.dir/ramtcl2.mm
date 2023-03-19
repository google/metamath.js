include "cn0.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cram.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "cpnf.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "ramcl2lem.mm"
include "eleq1d.mm"
include "pnfnre.mm"
include "neli.mm"
include "iftrue.mm"
include "nn0re.mm"
include "syl6bi.mm"
include "mtoi.mm"
include "necon2ai.mm"
include "ramtcl.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
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
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "syl6bir.mm"
include "impbid.mm"

theorem ramtcl2
  let vx: setvar x
  let cC: class C
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cV: class V
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  let vm: setvar m
  let vr: setvar r
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cN: class N
  assume ramval.c: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )
  assume ramval.t: |- T = { n e. NN0 | A. s ( n <_ ( # ` s ) -> A. f e. ( R ^m ( s C M ) ) E. c e. R E. x e. ~P s ( ( F ` c ) <_ ( # ` x ) /\ ( x C M ) C_ ( `' f " { c } ) ) ) }

  disjoint c f
  disjoint c x
  disjoint C c
  disjoint f x
  disjoint C f
  disjoint C x
  disjoint c n
  disjoint c s
  disjoint F c
  disjoint f n
  disjoint f s
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
  disjoint V c
  disjoint V f
  disjoint V n
  disjoint V s
  disjoint V x
  disjoint c y
  disjoint f y
  disjoint x y
  disjoint C y
  disjoint c m
  disjoint c r
  disjoint c z
  disjoint f m
  disjoint f r
  disjoint f z
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n r
  disjoint n y
  disjoint n z
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint s y
  disjoint s z
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a m
  disjoint a r
  disjoint a y
  disjoint a z
  disjoint b m
  disjoint b r
  disjoint b y
  disjoint b z
  disjoint i m
  disjoint i r
  disjoint i y
  disjoint i z
  disjoint M m
  disjoint M r
  disjoint M y
  disjoint M z
  disjoint A a
  disjoint A i
  disjoint A x
  disjoint B a
  disjoint B i
  disjoint B x
  disjoint R m
  disjoint R r
  disjoint R y
  disjoint R z
  disjoint T m
  disjoint T r
  disjoint T y
  disjoint T z
  disjoint N a
  disjoint N i
  disjoint N x
  disjoint V m
  disjoint V r
  disjoint V y
  disjoint V z
  assert |- ( ( M e. NN0 /\ R e. V /\ F : R --> NN0 ) -> ( ( M Ramsey F ) e. NN0 <-> T =/= (/) ) )

  proof
    cM
    cn0
    wcel
    cR
    cV
    wcel
    cR
    cn0
    cF
    wf
    w3a
    #
    cM
    cF
    cram
    co
    #
    cn0
    wcel
    #
    cT
    c0
    wne
    #
    @0
    @2
    cT
    c0
    wceq
    #
    cpnf
    cT
    cr
    clt
    cinf
    #
    cif
    #
    cn0
    wcel
    #
    @3
    @0
    @1
    @6
    cn0
    vx
    cC
    cR
    cT
    vf
    vi
    vn
    cF
    cM
    cV
    vs
    va
    vb
    vc
    ramval.c
    ramval.t
    ramcl2lem
    eleq1d
    @7
    cT
    c0
    @4
    @7
    cpnf
    cr
    wcel
    #
    cpnf
    cr
    pnfnre
    neli
    @4
    @7
    cpnf
    cn0
    wcel
    @8
    @4
    @6
    cpnf
    cn0
    @4
    cpnf
    @5
    iftrue
    eleq1d
    cpnf
    nn0re
    syl6bi
    mtoi
    necon2ai
    syl6bi
    @0
    @3
    @1
    cT
    wcel
    @2
    vx
    cC
    cR
    cT
    vf
    vi
    vn
    cF
    cM
    cV
    vs
    va
    vb
    vc
    ramval.c
    ramval.t
    ramtcl
    cT
    cn0
    @1
    cT
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
    @11
    cM
    cC
    co
    vf
    cv
    ccnv
    @10
    csn
    cima
    wss
    wa
    vx
    @9
    cpw
    wrex
    vc
    cR
    wrex
    vf
    cR
    @9
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
    cn0
    ramval.t
    @12
    vn
    cn0
    ssrab2
    eqsstri
    sseli
    syl6bir
    impbid
end
