include "cch.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "cph.mm"
include "co.mm"
include "chil.mm"
include "csh.mm"
include "wss.mm"
include "chsh.mm"
include "shocsh.mm"
include "syl.mm"
include "shsss.mm"
include "syl2anc.mm"
include "cv.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "cif.mm"
include "fveq2.mm"
include "rexeqdv.mm"
include "rexeqbi1dv.mm"
include "imbi2d.mm"
include "ifchhv.mm"
include "id.mm"
include "pjhthlem2.mm"
include "dedth.mm"
include "wb.mm"
include "shsel.mm"
include "sylibrd.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem pjhth
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( H e. CH -> ( H +H ( _|_ ` H ) ) = ~H )

  proof
    cH
    cch
    wcel
    #
    cH
    cH
    cort
    cfv
    #
    cph
    co
    #
    chil
    @0
    cH
    csh
    wcel
    #
    @1
    csh
    wcel
    #
    @2
    chil
    wss
    cH
    chsh
    #
    @0
    @3
    @4
    @5
    cH
    shocsh
    syl
    #
    cH
    @1
    shsss
    syl2anc
    @0
    vx
    chil
    @2
    @0
    vx
    cv
    #
    chil
    wcel
    #
    @7
    vy
    cv
    vz
    cv
    cva
    co
    wceq
    #
    vz
    @1
    wrex
    #
    vy
    cH
    wrex
    #
    @7
    @2
    wcel
    #
    @0
    @8
    @11
    wi
    @8
    @9
    vz
    @0
    cH
    chil
    cif
    #
    cort
    cfv
    #
    wrex
    #
    vy
    @13
    wrex
    #
    wi
    cH
    chil
    cH
    @13
    wceq
    #
    @11
    @16
    @8
    @10
    @15
    vy
    cH
    @13
    @17
    @9
    vz
    @1
    @14
    cH
    @13
    cort
    fveq2
    rexeqdv
    rexeqbi1dv
    imbi2d
    @8
    vy
    vz
    @7
    @13
    cH
    ifchhv
    @8
    id
    pjhthlem2
    dedth
    @0
    @3
    @4
    @12
    @11
    wb
    @5
    @6
    vy
    vz
    cH
    @1
    @7
    shsel
    syl2anc
    sylibrd
    ssrdv
    eqssd
end
