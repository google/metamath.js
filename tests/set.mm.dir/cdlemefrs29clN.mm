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
include "crio.mm"
include "wb.mm"
include "simpl11.mm"
include "simpl2r.mm"
include "simpl3.mm"
include "simpr.mm"
include "cdlemefrs29pre00.mm"
include "syl31anc.mm"
include "imbi1d.mm"
include "ralbidva.mm"
include "riotabidv.mm"
include "syl6reqr.mm"
include "wreu.mm"
include "cdlemefrs29cpre1.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem cdlemefrs29clN
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
  assume cdlemefrs29cl.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( R ./\ W ) ) = R ) -> z = ( N .\/ ( R ./\ W ) ) ) )

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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ ps ) -> O e. B )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    wps
    w3a
    #
    cO
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    wph
    wa
    @8
    cR
    cW
    c.an
    co
    #
    c.or
    co
    cR
    wceq
    #
    wa
    #
    vz
    cv
    cN
    @10
    c.or
    co
    wceq
    #
    wi
    #
    vs
    cA
    wral
    #
    vz
    cB
    crio
    #
    cB
    @7
    @16
    @9
    @11
    wa
    #
    @13
    wi
    #
    vs
    cA
    wral
    #
    vz
    cB
    crio
    cO
    @7
    @15
    @19
    vz
    cB
    @7
    @14
    @18
    vs
    cA
    @7
    @8
    cA
    wcel
    #
    wa
    #
    @12
    @17
    @13
    @21
    @0
    @5
    wps
    @20
    @12
    @17
    wb
    @0
    @1
    @2
    @6
    wps
    @20
    simpl11
    @4
    @5
    @3
    wps
    @20
    simpl2r
    @3
    @6
    wps
    @20
    simpl3
    @7
    @20
    simpr
    wph
    wps
    cA
    cB
    cR
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vs
    cdlemefrs27.b
    cdlemefrs27.l
    cdlemefrs27.j
    cdlemefrs27.m
    cdlemefrs27.a
    cdlemefrs27.h
    cdlemefrs27.eq
    cdlemefrs29pre00
    syl31anc
    imbi1d
    ralbidva
    riotabidv
    cdlemefrs29cl.o
    syl6reqr
    @7
    @15
    vz
    cB
    wreu
    @16
    cB
    wcel
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
    cdlemefrs27.rnb
    cdlemefrs29cpre1
    @15
    vz
    cB
    riotacl
    syl
    eqeltrd
end
