include "c0.mm"
include "wceq.mm"
include "cram.mm"
include "co.mm"
include "cpnf.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "cn0.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "eqeq2.mm"
include "cxr.mm"
include "ramval.mm"
include "infeq1.mm"
include "xrinf0.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "wa.mm"
include "adantr.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "cpw.mm"
include "wrex.mm"
include "cmap.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nn0ssre.mm"
include "sstri.mm"
include "cc0.mm"
include "cuz.mm"
include "nn0uz.mm"
include "sseqtri.mm"
include "infssuzcl.mm"
include "sylan.mm"
include "sseldi.mm"
include "rexrd.mm"
include "simpr.mm"
include "infssuzle.mm"
include "sylancr.mm"
include "sselda.mm"
include "lenltd.mm"
include "mpbid.mm"
include "infmin.mm"
include "eqtrd.mm"
include "sylan2br.mm"
include "ifbothda.mm"

theorem ramcl2lem
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
  assert |- ( ( M e. NN0 /\ R e. V /\ F : R --> NN0 ) -> ( M Ramsey F ) = if ( T = (/) , +oo , inf ( T , RR , < ) ) )

  proof
    cT
    c0
    wceq
    #
    cM
    cF
    cram
    co
    #
    cpnf
    wceq
    @1
    cT
    cr
    clt
    cinf
    #
    wceq
    #
    @1
    @0
    cpnf
    @2
    cif
    #
    wceq
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
    cpnf
    @2
    cpnf
    @4
    @1
    eqeq2
    @2
    @4
    @1
    eqeq2
    @5
    @0
    @1
    cT
    cxr
    clt
    cinf
    #
    cpnf
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
    ramval
    #
    @0
    @6
    c0
    cxr
    clt
    cinf
    cpnf
    cxr
    cT
    c0
    clt
    infeq1
    xrinf0
    syl6eq
    sylan9eq
    @0
    wn
    @5
    cT
    c0
    wne
    #
    @3
    cT
    c0
    df-ne
    @5
    @8
    wa
    #
    @1
    @6
    @2
    @5
    @1
    @6
    wceq
    @8
    @7
    adantr
    @9
    vz
    cxr
    cT
    @2
    clt
    cxr
    clt
    wor
    @9
    xrltso
    a1i
    @9
    @2
    @9
    cT
    cr
    @2
    cT
    cn0
    cr
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
    @12
    cM
    cC
    co
    vf
    cv
    ccnv
    @11
    csn
    cima
    wss
    wa
    vx
    @10
    cpw
    wrex
    vc
    cR
    wrex
    vf
    cR
    @10
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
    @13
    vn
    cn0
    ssrab2
    eqsstri
    #
    nn0ssre
    sstri
    #
    @5
    cT
    cc0
    cuz
    cfv
    #
    wss
    #
    @8
    @2
    cT
    wcel
    @17
    @5
    cT
    cn0
    @16
    @14
    nn0uz
    sseqtri
    #
    a1i
    cT
    cc0
    infssuzcl
    sylan
    #
    sseldi
    #
    rexrd
    @19
    @9
    vz
    cv
    #
    cT
    wcel
    #
    wa
    #
    @2
    @21
    cle
    wbr
    #
    @21
    @2
    clt
    wbr
    wn
    @23
    @17
    @22
    @24
    @18
    @9
    @22
    simpr
    @21
    cT
    cc0
    infssuzle
    sylancr
    @23
    @2
    @21
    @9
    @2
    cr
    wcel
    @22
    @20
    adantr
    @9
    cT
    cr
    @21
    cT
    cr
    wss
    @9
    @15
    a1i
    sselda
    lenltd
    mpbid
    infmin
    eqtrd
    sylan2br
    ifbothda
end
