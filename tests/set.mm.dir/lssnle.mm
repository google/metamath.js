include "wss.mm"
include "wn.mm"
include "co.mm"
include "wne.mm"
include "wpss.mm"
include "wceq.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wb.mm"
include "lsmss2b.mm"
include "syl2anc.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "necon3bbid.mm"
include "lsmub1.mm"
include "df-pss.mm"
include "baib.mm"
include "syl.mm"
include "bitr4d.mm"

theorem lssnle
  let wph: wff ph
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  assume lssnle.p: |- .(+) = ( LSSum ` G )
  assume lssnle.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume lssnle.u: |- ( ph -> U e. ( SubGrp ` G ) )


  assert |- ( ph -> ( -. U C_ T <-> T C. ( T .(+) U ) ) )

  proof
    wph
    cU
    cT
    wss
    #
    wn
    cT
    cT
    cU
    c.po
    co
    #
    wne
    #
    cT
    @1
    wpss
    #
    wph
    @0
    cT
    @1
    wph
    @0
    @1
    cT
    wceq
    #
    cT
    @1
    wceq
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @5
    wcel
    #
    @0
    @4
    wb
    lssnle.t
    lssnle.u
    c.po
    cT
    cU
    cG
    lssnle.p
    lsmss2b
    syl2anc
    @1
    cT
    eqcom
    syl6bb
    necon3bbid
    wph
    cT
    @1
    wss
    #
    @3
    @2
    wb
    wph
    @6
    @7
    @8
    lssnle.t
    lssnle.u
    c.po
    cT
    cU
    cG
    lssnle.p
    lsmub1
    syl2anc
    @3
    @8
    @2
    cT
    @1
    df-pss
    baib
    syl
    bitr4d
end
