include "wbr.mm"
include "cr1p.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "crg.mm"
include "wcel.mm"
include "cuc1p.mm"
include "wb.mm"
include "cnzr.mm"
include "nzrring.mm"
include "syl.mm"
include "cmn1.mm"
include "cdg1.mm"
include "c1.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "eqid.mm"
include "ply1remlem.mm"
include "simp1d.mm"
include "mon1puc1p.mm"
include "syl2anc.mm"
include "dvdsr1p.mm"
include "syl3anc.mm"
include "ply1rem.mm"
include "ply1scl0.mm"
include "eqcomd.mm"
include "eqeq12d.mm"
include "wf1.mm"
include "ply1sclf1.mm"
include "fveval1fvcl.mm"
include "ring0cl.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "3bitrd.mm"

theorem facth1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pa: class .||
  let cP: class P
  let cR: class R
  let cF: class F
  let cG: class G
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  assume ply1rem.p: |- P = ( Poly1 ` R )
  assume ply1rem.b: |- B = ( Base ` P )
  assume ply1rem.k: |- K = ( Base ` R )
  assume ply1rem.x: |- X = ( var1 ` R )
  assume ply1rem.m: |- .- = ( -g ` P )
  assume ply1rem.a: |- A = ( algSc ` P )
  assume ply1rem.g: |- G = ( X .- ( A ` N ) )
  assume ply1rem.o: |- O = ( eval1 ` R )
  assume ply1rem.1: |- ( ph -> R e. NzRing )
  assume ply1rem.2: |- ( ph -> R e. CRing )
  assume ply1rem.3: |- ( ph -> N e. K )
  assume ply1rem.4: |- ( ph -> F e. B )
  assume facth1.z: |- .0. = ( 0g ` R )
  assume facth1.d: |- .|| = ( ||r ` P )


  assert |- ( ph -> ( G .|| F <-> ( ( O ` F ) ` N ) = .0. ) )

  proof
    wph
    cG
    cF
    c.pa
    wbr
    #
    cF
    cG
    cR
    cr1p
    cfv
    #
    co
    #
    cP
    c0g
    cfv
    #
    wceq
    #
    cN
    cF
    cO
    cfv
    cfv
    #
    cA
    cfv
    #
    c.0
    cA
    cfv
    #
    wceq
    #
    @5
    c.0
    wceq
    #
    wph
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    cG
    cR
    cuc1p
    cfv
    #
    wcel
    #
    @0
    @4
    wb
    wph
    cR
    cnzr
    wcel
    @10
    ply1rem.1
    cR
    nzrring
    syl
    #
    ply1rem.4
    wph
    @10
    cG
    cR
    cmn1
    cfv
    #
    wcel
    #
    @12
    @13
    wph
    @15
    cG
    cR
    cdg1
    cfv
    #
    cfv
    c1
    wceq
    cG
    cO
    cfv
    ccnv
    c.0
    csn
    cima
    cN
    csn
    wceq
    wph
    cA
    cB
    @16
    cP
    cR
    @14
    cG
    cK
    c.mi
    cN
    cO
    cX
    c.0
    ply1rem.p
    ply1rem.b
    ply1rem.k
    ply1rem.x
    ply1rem.m
    ply1rem.a
    ply1rem.g
    ply1rem.o
    ply1rem.1
    ply1rem.2
    ply1rem.3
    @14
    eqid
    #
    @16
    eqid
    facth1.z
    ply1remlem
    simp1d
    @11
    cR
    @14
    cG
    @11
    eqid
    #
    @17
    mon1puc1p
    syl2anc
    cB
    @11
    c.pa
    cP
    cR
    @1
    cF
    cG
    @3
    ply1rem.p
    facth1.d
    ply1rem.b
    @18
    @3
    eqid
    #
    @1
    eqid
    #
    dvdsr1p
    syl3anc
    wph
    @2
    @6
    @3
    @7
    wph
    cA
    cB
    cP
    cR
    @1
    cF
    cG
    cK
    c.mi
    cN
    cO
    cX
    ply1rem.p
    ply1rem.b
    ply1rem.k
    ply1rem.x
    ply1rem.m
    ply1rem.a
    ply1rem.g
    ply1rem.o
    ply1rem.1
    ply1rem.2
    ply1rem.3
    ply1rem.4
    @20
    ply1rem
    wph
    @7
    @3
    wph
    @10
    @7
    @3
    wceq
    @13
    cA
    cP
    cR
    @3
    c.0
    ply1rem.p
    ply1rem.a
    facth1.z
    @19
    ply1scl0
    syl
    eqcomd
    eqeq12d
    wph
    cK
    cB
    cA
    wf1
    #
    @5
    cK
    wcel
    c.0
    cK
    wcel
    #
    @8
    @9
    wb
    wph
    @10
    @21
    @13
    cA
    cB
    cP
    cR
    cK
    ply1rem.p
    ply1rem.a
    ply1rem.k
    ply1rem.b
    ply1sclf1
    syl
    wph
    cK
    cP
    cR
    cB
    cF
    cO
    cN
    ply1rem.o
    ply1rem.p
    ply1rem.k
    ply1rem.b
    ply1rem.2
    ply1rem.3
    ply1rem.4
    fveval1fvcl
    wph
    @10
    @22
    @13
    cK
    cR
    c.0
    ply1rem.k
    facth1.z
    ring0cl
    syl
    cK
    cB
    @5
    c.0
    cA
    f1fveq
    syl12anc
    3bitrd
end
