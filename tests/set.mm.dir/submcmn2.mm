include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cbs.mm"
include "wss.mm"
include "ccmn.mm"
include "submbas.mm"
include "eqid.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "wb.mm"
include "submss.mm"
include "sscntz.mm"
include "syl2anc.mm"
include "cmnd.mm"
include "submmnd.mm"
include "iscmn.mm"
include "baib.mm"
include "syl.mm"
include "3bitr4rd.mm"

theorem submcmn2
  let cS: class S
  let cG: class G
  let cH: class H
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume subgabl.h: |- H = ( G |`s S )
  assume submcmn2.z: |- Z = ( Cntz ` G )


  assert |- ( S e. ( SubMnd ` G ) -> ( H e. CMnd <-> S C_ ( Z ` S ) ) )

  proof
    cS
    cG
    csubmnd
    cfv
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @3
    @2
    @4
    co
    #
    wceq
    #
    vy
    cS
    wral
    #
    vx
    cS
    wral
    #
    @2
    @3
    cH
    cplusg
    cfv
    #
    co
    #
    @3
    @2
    @10
    co
    #
    wceq
    #
    vy
    cH
    cbs
    cfv
    #
    wral
    #
    vx
    @14
    wral
    #
    cS
    cS
    cZ
    cfv
    wss
    #
    cH
    ccmn
    wcel
    #
    @1
    @8
    @15
    vx
    cS
    @14
    cS
    cH
    cG
    subgabl.h
    submbas
    #
    @1
    @7
    @13
    vy
    cS
    @14
    @19
    @1
    @5
    @11
    @6
    @12
    @1
    @4
    @10
    @2
    @3
    cS
    @4
    cG
    cH
    @0
    subgabl.h
    @4
    eqid
    #
    ressplusg
    #
    oveqd
    @1
    @4
    @10
    @3
    @2
    @21
    oveqd
    eqeq12d
    raleqbidv
    raleqbidv
    @1
    cS
    cG
    cbs
    cfv
    #
    wss
    #
    @23
    @17
    @9
    wb
    @22
    cS
    cG
    @22
    eqid
    #
    submss
    #
    @25
    vx
    vy
    @22
    @4
    cS
    cS
    cG
    cZ
    @24
    @20
    submcmn2.z
    sscntz
    syl2anc
    @1
    cH
    cmnd
    wcel
    #
    @18
    @16
    wb
    cS
    cH
    cG
    subgabl.h
    submmnd
    @18
    @26
    @16
    vx
    vy
    @14
    @10
    cH
    @14
    eqid
    @10
    eqid
    iscmn
    baib
    syl
    3bitr4rd
end
