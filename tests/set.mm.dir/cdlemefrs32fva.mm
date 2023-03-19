include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "csb.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "simp2rl.mm"
include "atbase.mm"
include "eqid.mm"
include "cdleme31so.mm"
include "3syl.mm"
include "wss.mm"
include "wrex.mm"
include "wreu.mm"
include "ssid.mm"
include "a1i.mm"
include "simpll.mm"
include "simpr.mm"
include "jca.mm"
include "imim1i.mm"
include "ralimi.mm"
include "rgenw.mm"
include "cdlemefrs29bpre1.mm"
include "wb.mm"
include "simpl11.mm"
include "simpl2r.mm"
include "simpl3.mm"
include "cdlemefrs29pre00.mm"
include "syl31anc.mm"
include "imbi1d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "mpbid.mm"
include "cdlemefrs29cpre1.mm"
include "riotass2.mm"
include "syl22anc.mm"
include "cdlemefrs29bpre0.mm"
include "adantr.mm"
include "riota5.mm"
include "3eqtrd.mm"

theorem cdlemefrs32fva
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
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
  assume cdleme29frs.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )

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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ ps ) -> [_ R / x ]_ O = [_ R / s ]_ N )

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
    #
    wps
    w3a
    #
    vx
    cR
    cO
    csb
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @11
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
    #
    cN
    @13
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
    @12
    wph
    wa
    #
    @14
    wa
    #
    @17
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
    vs
    cR
    cN
    csb
    #
    @9
    @5
    cR
    cB
    wcel
    @10
    @20
    wceq
    @5
    @6
    @4
    @3
    wps
    simp2rl
    cA
    cB
    cR
    cK
    cdlemefrs27.b
    cdlemefrs27.a
    atbase
    vx
    vz
    cA
    cB
    @20
    c.or
    c.le
    c.an
    cN
    cO
    cW
    cR
    vs
    cdleme29frs.o
    @20
    eqid
    cdleme31so
    3syl
    @9
    cB
    cB
    wss
    #
    @19
    @24
    wi
    #
    vz
    cB
    wral
    #
    @19
    vz
    cB
    wrex
    #
    @24
    vz
    cB
    wreu
    @20
    @25
    wceq
    @27
    @9
    cB
    ssid
    a1i
    @29
    @9
    @28
    vz
    cB
    @18
    @23
    vs
    cA
    @22
    @15
    @17
    @22
    @12
    @14
    @12
    wph
    @14
    simpll
    @21
    @14
    simpr
    jca
    imim1i
    ralimi
    rgenw
    a1i
    @9
    @24
    vz
    cB
    wrex
    @30
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
    cdlemefrs29bpre1
    @9
    @24
    @19
    vz
    cB
    @9
    @23
    @18
    vs
    cA
    @9
    @11
    cA
    wcel
    #
    wa
    #
    @22
    @15
    @17
    @32
    @0
    @7
    wps
    @31
    @22
    @15
    wb
    @0
    @1
    @2
    @8
    wps
    @31
    simpl11
    @4
    @7
    @3
    wps
    @31
    simpl2r
    @3
    @8
    wps
    @31
    simpl3
    @9
    @31
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
    rexbidv
    mpbid
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
    @19
    @24
    vz
    cB
    cB
    riotass2
    syl22anc
    @9
    @24
    vz
    cB
    @26
    cdlemefrs27.rnb
    @9
    @24
    @16
    @26
    wceq
    wb
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
    cdlemefrs29bpre0
    adantr
    riota5
    3eqtrd
end
