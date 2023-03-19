include "con0.mm"
include "c2o.mm"
include "cdif.mm"
include "wcel.mm"
include "c1o.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "coe.mm"
include "co.mm"
include "wss.mm"
include "oecl.mm"
include "syl2anc.mm"
include "onelon.mm"
include "ondif1.mm"
include "sylanbrc.mm"
include "eldifbd.mm"
include "ssel.mm"
include "syl5com.mm"
include "mtod.mm"
include "oe0m.mm"
include "syl.mm"
include "difss.mm"
include "syl6eqss.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "syl5ibrcom.mm"
include "oe1m.mm"
include "eqimss.mm"
include "3syl.mm"
include "jaod.mm"
include "cpr.mm"
include "elpri.mm"
include "df2o3.mm"
include "eleq2s.mm"
include "nsyl.mm"
include "eldifd.mm"
include "jca.mm"

theorem cantnflem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cD: class D
  let cM: class M
  let cF: class F
  let cZ: class Z
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume oemapval.t: |- T = { <. x , y >. | E. z e. B ( ( x ` z ) e. ( y ` z ) /\ A. w e. B ( z e. w -> ( x ` w ) = ( y ` w ) ) ) }
  assume cantnf.c: |- ( ph -> C e. ( A ^o B ) )
  assume cantnf.s: |- ( ph -> C C_ ran ( A CNF B ) )
  assume cantnf.e: |- ( ph -> (/) e. C )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c n
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint h k
  disjoint h n
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a g
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b c
  disjoint b d
  disjoint b g
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint c d
  disjoint C c
  disjoint d g
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint C d
  disjoint C g
  disjoint D k
  disjoint D n
  disjoint D z
  disjoint a f
  disjoint a h
  disjoint a k
  disjoint a n
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint A a
  disjoint b f
  disjoint b h
  disjoint b k
  disjoint b n
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint A b
  disjoint A c
  disjoint d f
  disjoint d h
  disjoint d k
  disjoint d n
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint A d
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A k
  disjoint A n
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint M x
  disjoint M y
  disjoint T c
  disjoint T f
  disjoint T g
  disjoint T k
  disjoint T t
  disjoint T u
  disjoint T v
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S c
  disjoint S f
  disjoint S g
  disjoint S k
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint Z g
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint G c
  disjoint G f
  disjoint G h
  disjoint G k
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H h
  disjoint H u
  disjoint H v
  disjoint H x
  disjoint H y
  disjoint K k
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K z
  disjoint O k
  disjoint O u
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint Y k
  disjoint Y t
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint X a
  disjoint X b
  disjoint X d
  disjoint X k
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( A e. ( On \ 2o ) /\ C e. ( On \ 1o ) ) )

  proof
    wph
    cA
    con0
    c2o
    cdif
    wcel
    cC
    con0
    c1o
    cdif
    wcel
    #
    wph
    cA
    con0
    c2o
    cantnfs.a
    wph
    cA
    c0
    wceq
    #
    cA
    c1o
    wceq
    #
    wo
    #
    cA
    c2o
    wcel
    wph
    @3
    cA
    cB
    coe
    co
    #
    c1o
    wss
    #
    wph
    @5
    cC
    c1o
    wcel
    #
    wph
    cC
    con0
    c1o
    wph
    cC
    con0
    wcel
    #
    c0
    cC
    wcel
    @0
    wph
    @4
    con0
    wcel
    #
    cC
    @4
    wcel
    #
    @7
    wph
    cA
    con0
    wcel
    cB
    con0
    wcel
    #
    @8
    cantnfs.a
    cantnfs.b
    cA
    cB
    oecl
    syl2anc
    cantnf.c
    @4
    cC
    onelon
    syl2anc
    cantnf.e
    cC
    ondif1
    sylanbrc
    #
    eldifbd
    wph
    @9
    @5
    @6
    cantnf.c
    @4
    c1o
    cC
    ssel
    syl5com
    mtod
    wph
    @1
    @5
    @2
    wph
    @5
    @1
    c0
    cB
    coe
    co
    #
    c1o
    wss
    wph
    @12
    c1o
    cB
    cdif
    #
    c1o
    wph
    @10
    @12
    @13
    wceq
    cantnfs.b
    cB
    oe0m
    syl
    c1o
    cB
    difss
    syl6eqss
    @1
    @4
    @12
    c1o
    cA
    c0
    cB
    coe
    oveq1
    sseq1d
    syl5ibrcom
    wph
    @5
    @2
    c1o
    cB
    coe
    co
    #
    c1o
    wss
    #
    wph
    @10
    @14
    c1o
    wceq
    @15
    cantnfs.b
    cB
    oe1m
    @14
    c1o
    eqimss
    3syl
    @2
    @4
    @14
    c1o
    cA
    c1o
    cB
    coe
    oveq1
    sseq1d
    syl5ibrcom
    jaod
    mtod
    @3
    cA
    c0
    c1o
    cpr
    c2o
    cA
    c0
    c1o
    elpri
    df2o3
    eleq2s
    nsyl
    eldifd
    @11
    jca
end
