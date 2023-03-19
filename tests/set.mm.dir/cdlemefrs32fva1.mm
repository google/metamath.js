include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "csb.mm"
include "wceq.mm"
include "simp2rl.mm"
include "atbase.mm"
include "syl.mm"
include "simp2l.mm"
include "simp2rr.mm"
include "cdleme31fv1s.mm"
include "syl12anc.mm"
include "cdlemefrs32fva.mm"
include "eqtrd.mm"

theorem cdlemefrs32fva1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let vs: setvar s
  assume cdlemefrs27.b: |- B = ( Base ` K )
  assume cdlemefrs27.l: |- .<_ = ( le ` K )
  assume cdlemefrs27.j: |- .\/ = ( join ` K )
  assume cdlemefrs27.m: |- ./\ = ( meet ` K )
  assume cdlemefrs27.a: |- A = ( Atoms ` K )
  assume cdlemefrs27.h: |- H = ( LHyp ` K )
  assume cdlemefrs27.eq: |- ( s = R -> ( ph <-> ps ) )
  assume cdlemefrs27.nb: |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ P =/= Q /\ ( s e. A /\ ( -. s .<_ W /\ ph ) ) ) -> N e. B )
  assume cdlemefrs27.rnb: |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ ps ) -> [_ R / s ]_ N e. B )
  assume cdleme29frs.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme29frs.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )

  disjoint s z
  disjoint A s
  disjoint H s
  disjoint .\/ s
  disjoint K s
  disjoint .<_ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint W s
  disjoint ps s
  disjoint A z
  disjoint B z
  disjoint H z
  disjoint K z
  disjoint .<_ z
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint R z
  disjoint W z
  disjoint ps z
  disjoint B s
  disjoint .\/ z
  disjoint ./\ s
  disjoint ./\ z
  disjoint ph z
  disjoint x z
  disjoint A x
  disjoint B x
  disjoint .\/ x
  disjoint .<_ x
  disjoint ./\ x
  disjoint N x
  disjoint s x
  disjoint R x
  disjoint W x
  disjoint P x
  disjoint Q x
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ ps ) -> ( F ` R ) = [_ R / s ]_ N )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cP
    cQ
    wne
    #
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    wps
    w3a
    #
    cR
    cF
    cfv
    #
    vx
    cR
    cO
    csb
    #
    vs
    cR
    cN
    csb
    @5
    cR
    cB
    wcel
    #
    @1
    @3
    @6
    @7
    wceq
    @5
    @2
    @8
    @2
    @3
    @1
    @0
    wps
    simp2rl
    cA
    cB
    cR
    cK
    cdlemefrs27.b
    cdlemefrs27.a
    atbase
    syl
    @0
    @1
    @4
    wps
    simp2l
    @2
    @3
    @1
    @0
    wps
    simp2rr
    vx
    vz
    cA
    cB
    cP
    cQ
    cF
    c.or
    c.le
    c.an
    cN
    cO
    cW
    cR
    vs
    cdleme29frs.o
    cdleme29frs.f
    cdleme31fv1s
    syl12anc
    wph
    wps
    vx
    vz
    cA
    cB
    cP
    cQ
    cR
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    vs
    cdlemefrs27.b
    cdlemefrs27.l
    cdlemefrs27.j
    cdlemefrs27.m
    cdlemefrs27.a
    cdlemefrs27.h
    cdlemefrs27.eq
    cdlemefrs27.nb
    cdlemefrs27.rnb
    cdleme29frs.o
    cdlemefrs32fva
    eqtrd
end
