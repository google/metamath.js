include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "csb.mm"
include "cdlemefrs29bpre0.mm"
include "rexbidv.mm"
include "risset.mm"
include "syl6bbr.mm"
include "mpbird.mm"

theorem cdlemefrs29bpre1
  let wph: wff ph
  let wps: wff ps
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ ps ) -> E. z e. B A. s e. A ( ( ( -. s .<_ W /\ ph ) /\ ( s .\/ ( R ./\ W ) ) = R ) -> z = ( N .\/ ( R ./\ W ) ) ) )

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
    cP
    cQ
    wne
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    wa
    wps
    w3a
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    wph
    wa
    @1
    cR
    cW
    c.an
    co
    #
    c.or
    co
    cR
    wceq
    wa
    vz
    cv
    #
    cN
    @2
    c.or
    co
    wceq
    wi
    vs
    cA
    wral
    #
    vz
    cB
    wrex
    #
    vs
    cR
    cN
    csb
    #
    cB
    wcel
    #
    cdlemefrs27.rnb
    @0
    @5
    @3
    @6
    wceq
    #
    vz
    cB
    wrex
    @7
    @0
    @4
    @8
    vz
    cB
    wph
    wps
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
    cdlemefrs29bpre0
    rexbidv
    vz
    @6
    cB
    risset
    syl6bbr
    mpbird
end
