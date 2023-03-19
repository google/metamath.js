include "cfv.mm"
include "wss.mm"
include "csubg.mm"
include "wcel.mm"
include "wb.mm"
include "cbs.mm"
include "eqid.mm"
include "subgss.mm"
include "cntzrec.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem cntzrecd
  let wph: wff ph
  let cT: class T
  let cU: class U
  let cG: class G
  let cZ: class Z
  assume cntzrecd.z: |- Z = ( Cntz ` G )
  assume cntzrecd.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume cntzrecd.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume cntzrecd.s: |- ( ph -> T C_ ( Z ` U ) )


  assert |- ( ph -> U C_ ( Z ` T ) )

  proof
    wph
    cT
    cU
    cZ
    cfv
    wss
    #
    cU
    cT
    cZ
    cfv
    wss
    #
    cntzrecd.s
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @2
    wcel
    #
    @0
    @1
    wb
    #
    cntzrecd.t
    cntzrecd.u
    @3
    cT
    cG
    cbs
    cfv
    #
    wss
    cU
    @6
    wss
    @5
    @4
    @6
    cT
    cG
    @6
    eqid
    #
    subgss
    @6
    cU
    cG
    @7
    subgss
    @6
    cT
    cU
    cG
    cZ
    @7
    cntzrecd.z
    cntzrec
    syl2an
    syl2anc
    mpbid
end
