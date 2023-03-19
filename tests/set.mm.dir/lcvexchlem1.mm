include "co.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "cin.mm"
include "wpss.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "clmod.mm"
include "lsssssubg.mm"
include "syl.mm"
include "sseldd.mm"
include "lsmub1.mm"
include "syl2anc.mm"
include "inss2.mm"
include "a1i.mm"
include "2thd.mm"
include "wceq.mm"
include "sseqin2.mm"
include "wb.mm"
include "lsmss2b.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "syl5rbbr.mm"
include "necon3bid.mm"
include "anbi12d.mm"
include "df-pss.mm"
include "3bitr4g.mm"

theorem lcvexchlem1
  let wph: wff ph
  let cC: class C
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let vr: setvar r
  let vs: setvar s
  assume lcvexch.s: |- S = ( LSubSp ` W )
  assume lcvexch.p: |- .(+) = ( LSSum ` W )
  assume lcvexch.c: |- C = ( <oL ` W )
  assume lcvexch.w: |- ( ph -> W e. LMod )
  assume lcvexch.t: |- ( ph -> T e. S )
  assume lcvexch.u: |- ( ph -> U e. S )


  assert |- ( ph -> ( T C. ( T .(+) U ) <-> ( T i^i U ) C. U ) )

  proof
    wph
    cT
    cT
    cU
    c.po
    co
    #
    wss
    #
    cT
    @0
    wne
    #
    wa
    cT
    cU
    cin
    #
    cU
    wss
    #
    @3
    cU
    wne
    #
    wa
    cT
    @0
    wpss
    @3
    cU
    wpss
    wph
    @1
    @4
    @2
    @5
    wph
    @1
    @4
    wph
    cT
    cW
    csubg
    cfv
    #
    wcel
    #
    cU
    @6
    wcel
    #
    @1
    wph
    cS
    @6
    cT
    wph
    cW
    clmod
    wcel
    cS
    @6
    wss
    lcvexch.w
    cS
    cW
    lcvexch.s
    lsssssubg
    syl
    #
    lcvexch.t
    sseldd
    #
    wph
    cS
    @6
    cU
    @9
    lcvexch.u
    sseldd
    #
    c.po
    cT
    cU
    cW
    lcvexch.p
    lsmub1
    syl2anc
    @4
    wph
    cT
    cU
    inss2
    a1i
    2thd
    wph
    cT
    @0
    @3
    cU
    @3
    cU
    wceq
    cU
    cT
    wss
    #
    wph
    cT
    @0
    wceq
    #
    cU
    cT
    sseqin2
    wph
    @12
    @0
    cT
    wceq
    #
    @13
    wph
    @7
    @8
    @12
    @14
    wb
    @10
    @11
    c.po
    cT
    cU
    cW
    lcvexch.p
    lsmss2b
    syl2anc
    @0
    cT
    eqcom
    syl6bb
    syl5rbbr
    necon3bid
    anbi12d
    cT
    @0
    df-pss
    @3
    cU
    df-pss
    3bitr4g
end
