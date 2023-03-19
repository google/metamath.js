include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cc.mm"
include "cnex.mm"
include "cr.mm"
include "wf.mm"
include "cxp.mm"
include "absf.mm"
include "subf.mm"
include "fco.mm"
include "mp2an.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "subcl.mm"
include "abs00ad.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "subeq0.mm"
include "3bitr3d.mm"
include "w3a.mm"
include "caddc.mm"
include "cle.mm"
include "abs3dif.mm"
include "abssub.mm"
include "oveq1d.mm"
include "3adant2.mm"
include "breqtrd.mm"
include "3adant3.mm"
include "oveq12d.mm"
include "3coml.mm"
include "3brtr4d.mm"
include "ismeti.mm"

theorem cnmet
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( abs o. - ) e. ( Met ` CC )

  proof
    vx
    vy
    vz
    cabs
    cmin
    ccom
    #
    cc
    cnex
    cc
    cr
    cabs
    wf
    cc
    cc
    cxp
    #
    cc
    cmin
    wf
    @1
    cr
    @0
    wf
    absf
    subf
    @1
    cc
    cr
    cabs
    cmin
    fco
    mp2an
    vx
    cv
    #
    cc
    wcel
    #
    vy
    cv
    #
    cc
    wcel
    #
    wa
    #
    @2
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    cc0
    wceq
    @7
    cc0
    wceq
    @2
    @4
    @0
    co
    #
    cc0
    wceq
    @2
    @4
    wceq
    @6
    @7
    @2
    @4
    subcl
    abs00ad
    @6
    @8
    @9
    cc0
    @6
    @9
    @8
    @2
    @4
    @0
    @0
    eqid
    #
    cnmetdval
    #
    eqcomd
    eqeq1d
    @2
    @4
    subeq0
    3bitr3d
    @3
    @5
    vz
    cv
    #
    cc
    wcel
    #
    w3a
    #
    @8
    @12
    @2
    cmin
    co
    cabs
    cfv
    #
    @12
    @4
    cmin
    co
    cabs
    cfv
    #
    caddc
    co
    #
    @9
    @12
    @2
    @0
    co
    #
    @12
    @4
    @0
    co
    #
    caddc
    co
    #
    cle
    @14
    @8
    @2
    @12
    cmin
    co
    cabs
    cfv
    #
    @16
    caddc
    co
    #
    @17
    cle
    @2
    @4
    @12
    abs3dif
    @3
    @13
    @22
    @17
    wceq
    @5
    @3
    @13
    wa
    @21
    @15
    @16
    caddc
    @2
    @12
    abssub
    oveq1d
    3adant2
    breqtrd
    @3
    @5
    @9
    @8
    wceq
    @13
    @11
    3adant3
    @13
    @3
    @5
    @20
    @17
    wceq
    @13
    @3
    @5
    w3a
    @18
    @15
    @19
    @16
    caddc
    @13
    @3
    @18
    @15
    wceq
    @5
    @12
    @2
    @0
    @10
    cnmetdval
    3adant3
    @13
    @5
    @19
    @16
    wceq
    @3
    @12
    @4
    @0
    @10
    cnmetdval
    3adant2
    oveq12d
    3coml
    3brtr4d
    ismeti
end
