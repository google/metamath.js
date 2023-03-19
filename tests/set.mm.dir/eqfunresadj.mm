include "wfun.mm"
include "wa.mm"
include "cres.mm"
include "wceq.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "w3a.mm"
include "csn.mm"
include "cun.mm"
include "relres.mm"
include "cv.mm"
include "wbr.mm"
include "wo.mm"
include "wb.mm"
include "breq.mm"
include "3ad2ant2.mm"
include "velsn.mm"
include "simp33.mm"
include "eqeq1d.mm"
include "simp1l.mm"
include "simp31.mm"
include "funbrfvb.mm"
include "syl2anc.mm"
include "simp1r.mm"
include "simp32.mm"
include "3bitr3d.mm"
include "breq1.mm"
include "bibi12d.mm"
include "syl5ibrcom.mm"
include "syl5bi.mm"
include "pm5.32rd.mm"
include "vex.mm"
include "brres.mm"
include "3bitr4g.mm"
include "orbi12d.mm"
include "resundi.mm"
include "breqi.mm"
include "brun.mm"
include "bitri.mm"
include "eqbrrdiv.mm"

theorem eqfunresadj
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( Fun F /\ Fun G ) /\ ( F |` X ) = ( G |` X ) /\ ( Y e. dom F /\ Y e. dom G /\ ( F ` Y ) = ( G ` Y ) ) ) -> ( F |` ( X u. { Y } ) ) = ( G |` ( X u. { Y } ) ) )

  proof
    cF
    wfun
    #
    cG
    wfun
    #
    wa
    #
    cF
    cX
    cres
    #
    cG
    cX
    cres
    #
    wceq
    #
    cY
    cF
    cdm
    wcel
    #
    cY
    cG
    cdm
    wcel
    #
    cY
    cF
    cfv
    #
    cY
    cG
    cfv
    #
    wceq
    #
    w3a
    #
    w3a
    #
    vx
    vy
    cF
    cX
    cY
    csn
    #
    cun
    #
    cres
    #
    cG
    @14
    cres
    #
    cF
    @14
    relres
    cG
    @14
    relres
    @12
    vx
    cv
    #
    vy
    cv
    #
    @3
    wbr
    #
    @17
    @18
    cF
    @13
    cres
    #
    wbr
    #
    wo
    #
    @17
    @18
    @4
    wbr
    #
    @17
    @18
    cG
    @13
    cres
    #
    wbr
    #
    wo
    #
    @17
    @18
    @15
    wbr
    #
    @17
    @18
    @16
    wbr
    #
    @12
    @19
    @23
    @21
    @25
    @5
    @2
    @19
    @23
    wb
    @11
    @17
    @18
    @3
    @4
    breq
    3ad2ant2
    @12
    @17
    @18
    cF
    wbr
    #
    @17
    @13
    wcel
    #
    wa
    @17
    @18
    cG
    wbr
    #
    @30
    wa
    @21
    @25
    @12
    @30
    @29
    @31
    @30
    @17
    cY
    wceq
    #
    @12
    @29
    @31
    wb
    #
    vx
    cY
    velsn
    @12
    @33
    @32
    cY
    @18
    cF
    wbr
    #
    cY
    @18
    cG
    wbr
    #
    wb
    @12
    @8
    @18
    wceq
    #
    @9
    @18
    wceq
    #
    @34
    @35
    @12
    @8
    @9
    @18
    @2
    @5
    @6
    @7
    @10
    simp33
    eqeq1d
    @12
    @0
    @6
    @36
    @34
    wb
    @0
    @1
    @5
    @11
    simp1l
    @2
    @5
    @6
    @7
    @10
    simp31
    cY
    @18
    cF
    funbrfvb
    syl2anc
    @12
    @1
    @7
    @37
    @35
    wb
    @0
    @1
    @5
    @11
    simp1r
    @2
    @5
    @6
    @7
    @10
    simp32
    cY
    @18
    cG
    funbrfvb
    syl2anc
    3bitr3d
    @32
    @29
    @34
    @31
    @35
    @17
    cY
    @18
    cF
    breq1
    @17
    cY
    @18
    cG
    breq1
    bibi12d
    syl5ibrcom
    syl5bi
    pm5.32rd
    @17
    @18
    cF
    @13
    vy
    vex
    #
    brres
    @17
    @18
    cG
    @13
    @38
    brres
    3bitr4g
    orbi12d
    @27
    @17
    @18
    @3
    @20
    cun
    #
    wbr
    @22
    @17
    @18
    @15
    @39
    cF
    cX
    @13
    resundi
    breqi
    @17
    @18
    @3
    @20
    brun
    bitri
    @28
    @17
    @18
    @4
    @24
    cun
    #
    wbr
    @26
    @17
    @18
    @16
    @40
    cG
    cX
    @13
    resundi
    breqi
    @17
    @18
    @4
    @24
    brun
    bitri
    3bitr4g
    eqbrrdiv
end
