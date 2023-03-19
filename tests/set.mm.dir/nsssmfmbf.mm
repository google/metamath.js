include "csmblfn.mm"
include "cfv.mm"
include "cmbf.mm"
include "wss.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cr.mm"
include "cpw.mm"
include "cvol.mm"
include "cdm.mm"
include "vitali2.mm"
include "pssnssi.mm"
include "nss.mm"
include "mpbi.mm"
include "cc0.mm"
include "cmpt.mm"
include "elpwi.mm"
include "adantr.mm"
include "eleq2i.mm"
include "bicomi.mm"
include "notbii.mm"
include "biimpi.mm"
include "adantl.mm"
include "eqid.mm"
include "nsssmfmbflem.mm"
include "exlimiv.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem nsssmfmbf
  let cS: class S
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume nsssmfmbf.1: |- S = dom vol


  assert |- -. ( SMblFn ` S ) C_ MblFn

  proof
    cS
    csmblfn
    cfv
    #
    cmbf
    wss
    wn
    vf
    cv
    #
    @0
    wcel
    @1
    cmbf
    wcel
    wn
    wa
    vf
    wex
    #
    vx
    cv
    #
    cr
    cpw
    #
    wcel
    #
    @3
    cvol
    cdm
    #
    wcel
    #
    wn
    #
    wa
    #
    vx
    wex
    #
    @2
    @4
    @6
    wss
    wn
    @10
    @6
    @4
    vitali2
    pssnssi
    vx
    @4
    @6
    nss
    mpbi
    @9
    @2
    vx
    @9
    vy
    cS
    vf
    vy
    @3
    cc0
    cmpt
    #
    @3
    nsssmfmbf.1
    @5
    @3
    cr
    wss
    @8
    @3
    cr
    elpwi
    adantr
    @8
    @3
    cS
    wcel
    #
    wn
    #
    @5
    @8
    @13
    @7
    @12
    @12
    @7
    cS
    @6
    @3
    nsssmfmbf.1
    eleq2i
    bicomi
    notbii
    biimpi
    adantl
    @11
    eqid
    nsssmfmbflem
    exlimiv
    ax-mp
    vf
    @0
    cmbf
    nss
    mpbir
end
