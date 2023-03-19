include "co.mm"
include "cress.mm"
include "clmhm.mm"
include "wcel.mm"
include "pj1lmhm.mm"
include "clmod.mm"
include "crn.mm"
include "wss.mm"
include "wb.mm"
include "wf.mm"
include "cplusg.mm"
include "cfv.mm"
include "ccntz.mm"
include "eqid.mm"
include "csubg.mm"
include "lsssssubg.mm"
include "syl.mm"
include "sseldd.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablcntzd.mm"
include "pj1f.mm"
include "frn.mm"
include "reslmhm2b.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem pj1lmhm2
  let wph: wff ph
  let cP: class P
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cL: class L
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume pj1lmhm.l: |- L = ( LSubSp ` W )
  assume pj1lmhm.s: |- .(+) = ( LSSum ` W )
  assume pj1lmhm.z: |- .0. = ( 0g ` W )
  assume pj1lmhm.p: |- P = ( proj1 ` W )
  assume pj1lmhm.1: |- ( ph -> W e. LMod )
  assume pj1lmhm.2: |- ( ph -> T e. L )
  assume pj1lmhm.3: |- ( ph -> U e. L )
  assume pj1lmhm.4: |- ( ph -> ( T i^i U ) = { .0. } )


  assert |- ( ph -> ( T P U ) e. ( ( W |`s ( T .(+) U ) ) LMHom ( W |`s T ) ) )

  proof
    wph
    cT
    cU
    cP
    co
    #
    cW
    cT
    cU
    c.po
    co
    #
    cress
    co
    #
    cW
    clmhm
    co
    wcel
    #
    @0
    @2
    cW
    cT
    cress
    co
    #
    clmhm
    co
    wcel
    #
    wph
    cP
    c.po
    cT
    cU
    cL
    cW
    c.0
    pj1lmhm.l
    pj1lmhm.s
    pj1lmhm.z
    pj1lmhm.p
    pj1lmhm.1
    pj1lmhm.2
    pj1lmhm.3
    pj1lmhm.4
    pj1lmhm
    wph
    cW
    clmod
    wcel
    #
    cT
    cL
    wcel
    @0
    crn
    cT
    wss
    #
    @3
    @5
    wb
    pj1lmhm.1
    pj1lmhm.2
    wph
    @1
    cT
    @0
    wf
    @7
    wph
    cP
    cW
    cplusg
    cfv
    #
    c.po
    cT
    cU
    cW
    c.0
    cW
    ccntz
    cfv
    #
    @8
    eqid
    pj1lmhm.s
    pj1lmhm.z
    @9
    eqid
    #
    wph
    cL
    cW
    csubg
    cfv
    #
    cT
    wph
    @6
    cL
    @11
    wss
    pj1lmhm.1
    cL
    cW
    pj1lmhm.l
    lsssssubg
    syl
    #
    pj1lmhm.2
    sseldd
    #
    wph
    cL
    @11
    cU
    @12
    pj1lmhm.3
    sseldd
    #
    pj1lmhm.4
    wph
    cT
    cU
    cW
    @9
    @10
    wph
    @6
    cW
    cabl
    wcel
    pj1lmhm.1
    cW
    lmodabl
    syl
    @13
    @14
    ablcntzd
    pj1lmhm.p
    pj1f
    @1
    cT
    @0
    frn
    syl
    @2
    cW
    @4
    @0
    cL
    cT
    @4
    eqid
    pj1lmhm.l
    reslmhm2b
    syl3anc
    mpbid
end
