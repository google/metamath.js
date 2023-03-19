include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cword.mm"
include "csubmnd.mm"
include "cfv.mm"
include "cbs.mm"
include "c0.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "sswrd.mm"
include "adantl.mm"
include "wceq.mm"
include "eqid.mm"
include "frmdbas.mm"
include "adantr.mm"
include "sseqtr4d.mm"
include "wrd0.mm"
include "a1i.mm"
include "cconcat.mm"
include "sselda.mm"
include "anim12dan.mm"
include "frmdadd.mm"
include "syl.mm"
include "ccatcl.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "cmnd.mm"
include "w3a.mm"
include "wb.mm"
include "frmdmnd.mm"
include "frmd0.mm"
include "issubm.mm"
include "mpbir3and.mm"

theorem frmdsssubm
  let cI: class I
  let cJ: class J
  let cM: class M
  let cV: class V
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let cW: class W
  assume frmdmnd.m: |- M = ( freeMnd ` I )


  assert |- ( ( I e. V /\ J C_ I ) -> Word J e. ( SubMnd ` M ) )

  proof
    cI
    cV
    wcel
    #
    cJ
    cI
    wss
    #
    wa
    #
    cJ
    cword
    #
    cM
    csubmnd
    cfv
    wcel
    #
    @3
    cM
    cbs
    cfv
    #
    wss
    #
    c0
    @3
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @3
    wcel
    #
    vy
    @3
    wral
    vx
    @3
    wral
    #
    @2
    @3
    cI
    cword
    #
    @5
    @1
    @3
    @14
    wss
    @0
    cJ
    cI
    sswrd
    adantl
    @0
    @5
    @14
    wceq
    @1
    @5
    cI
    cM
    cV
    frmdmnd.m
    @5
    eqid
    #
    frmdbas
    adantr
    sseqtr4d
    #
    @7
    @2
    cJ
    wrd0
    a1i
    @2
    @12
    vx
    vy
    @3
    @3
    @2
    @8
    @3
    wcel
    #
    @9
    @3
    wcel
    #
    wa
    #
    wa
    #
    @11
    @8
    @9
    cconcat
    co
    #
    @3
    @20
    @8
    @5
    wcel
    #
    @9
    @5
    wcel
    #
    wa
    @11
    @21
    wceq
    @2
    @17
    @22
    @18
    @23
    @2
    @3
    @5
    @8
    @16
    sselda
    @2
    @3
    @5
    @9
    @16
    sselda
    anim12dan
    @5
    @10
    cI
    cM
    @8
    @9
    frmdmnd.m
    @15
    @10
    eqid
    #
    frmdadd
    syl
    @19
    @21
    @3
    wcel
    @2
    cJ
    @8
    @9
    ccatcl
    adantl
    eqeltrd
    ralrimivva
    @2
    cM
    cmnd
    wcel
    #
    @4
    @6
    @7
    @13
    w3a
    wb
    @0
    @25
    @1
    cI
    cM
    cV
    frmdmnd.m
    frmdmnd
    adantr
    vx
    vy
    @5
    @10
    @3
    cM
    c0
    @15
    cI
    cM
    frmdmnd.m
    frmd0
    @24
    issubm
    syl
    mpbir3and
end
