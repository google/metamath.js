include "cbs.mm"
include "cfv.mm"
include "csubg.mm"
include "wcel.mm"
include "wss.mm"
include "eqid.mm"
include "subgss.mm"
include "syl.mm"
include "ccmn.mm"
include "wceq.mm"
include "cabl.mm"
include "ablcmn.mm"
include "cntzcmn.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"

theorem ablcntzd
  let wph: wff ph
  let cT: class T
  let cU: class U
  let cG: class G
  let cZ: class Z
  assume ablcntzd.z: |- Z = ( Cntz ` G )
  assume ablcntzd.a: |- ( ph -> G e. Abel )
  assume ablcntzd.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume ablcntzd.u: |- ( ph -> U e. ( SubGrp ` G ) )


  assert |- ( ph -> T C_ ( Z ` U ) )

  proof
    wph
    cT
    cG
    cbs
    cfv
    #
    cU
    cZ
    cfv
    #
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    cT
    @0
    wss
    ablcntzd.t
    @0
    cT
    cG
    @0
    eqid
    #
    subgss
    syl
    wph
    cG
    ccmn
    wcel
    #
    cU
    @0
    wss
    #
    @1
    @0
    wceq
    wph
    cG
    cabl
    wcel
    @4
    ablcntzd.a
    cG
    ablcmn
    syl
    wph
    cU
    @2
    wcel
    @5
    ablcntzd.u
    @0
    cU
    cG
    @3
    subgss
    syl
    @0
    cU
    cG
    cZ
    @3
    ablcntzd.z
    cntzcmn
    syl2anc
    sseqtr4d
end
