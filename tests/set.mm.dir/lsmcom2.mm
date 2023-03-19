include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "simp3.mm"
include "sselda.mm"
include "adantrr.mm"
include "simprr.mm"
include "eqid.mm"
include "cntzi.mm"
include "syl2anc.mm"
include "eqeq2d.mm"
include "2rexbidva.mm"
include "rexcom.mm"
include "syl6bb.mm"
include "wb.mm"
include "lsmelval.mm"
include "3adant3.mm"
include "ancoms.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem lsmcom2
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  assume lsmsubg.p: |- .(+) = ( LSSum ` G )
  assume lsmsubg.z: |- Z = ( Cntz ` G )


  assert |- ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) /\ T C_ ( Z ` U ) ) -> ( T .(+) U ) = ( U .(+) T ) )

  proof
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @0
    wcel
    #
    cT
    cU
    cZ
    cfv
    #
    wss
    #
    w3a
    #
    vx
    cT
    cU
    c.po
    co
    #
    cU
    cT
    c.po
    co
    #
    @5
    vx
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vb
    cU
    wrex
    va
    cT
    wrex
    #
    @8
    @10
    @9
    @11
    co
    #
    wceq
    #
    va
    cT
    wrex
    vb
    cU
    wrex
    #
    @8
    @6
    wcel
    #
    @8
    @7
    wcel
    #
    @5
    @14
    @16
    vb
    cU
    wrex
    va
    cT
    wrex
    @17
    @5
    @13
    @16
    va
    vb
    cT
    cU
    @5
    @9
    cT
    wcel
    #
    @10
    cU
    wcel
    #
    wa
    wa
    #
    @12
    @15
    @8
    @22
    @9
    @3
    wcel
    #
    @21
    @12
    @15
    wceq
    @5
    @20
    @23
    @21
    @5
    cT
    @3
    @9
    @1
    @2
    @4
    simp3
    sselda
    adantrr
    @5
    @20
    @21
    simprr
    @11
    cU
    cG
    @9
    @10
    cZ
    @11
    eqid
    #
    lsmsubg.z
    cntzi
    syl2anc
    eqeq2d
    2rexbidva
    @16
    va
    vb
    cT
    cU
    rexcom
    syl6bb
    @1
    @2
    @18
    @14
    wb
    @4
    va
    vb
    @11
    c.po
    cT
    cU
    cG
    @8
    @24
    lsmsubg.p
    lsmelval
    3adant3
    @1
    @2
    @19
    @17
    wb
    #
    @4
    @2
    @1
    @25
    vb
    va
    @11
    c.po
    cU
    cT
    cG
    @8
    @24
    lsmsubg.p
    lsmelval
    ancoms
    3adant3
    3bitr4d
    eqrdv
end
