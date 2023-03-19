include "cc.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "cdif.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "ccld.mm"
include "wcel.mm"
include "cr.mm"
include "crest.mm"
include "eqid.mm"
include "recld2.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "0re.mm"
include "iocmnfcld.mm"
include "ax-mp.mm"
include "tgioo2.mm"
include "fveq2i.mm"
include "eleqtri.mm"
include "restcldr.mm"
include "mp2an.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "cldopn.mm"
include "eqeltri.mm"

theorem logdmopn
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )


  assert |- D e. ( TopOpen ` CCfld )

  proof
    cD
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    #
    ccnfld
    ctopn
    cfv
    #
    logcn.d
    @0
    @2
    ccld
    cfv
    #
    wcel
    #
    @1
    @2
    wcel
    cr
    @3
    wcel
    @0
    @2
    cr
    crest
    co
    #
    ccld
    cfv
    #
    wcel
    @4
    @2
    @2
    eqid
    #
    recld2
    @0
    cioo
    crn
    ctg
    cfv
    #
    ccld
    cfv
    #
    @6
    cc0
    cr
    wcel
    @0
    @9
    wcel
    0re
    cc0
    iocmnfcld
    ax-mp
    @8
    @5
    ccld
    @2
    @7
    tgioo2
    fveq2i
    eleqtri
    cr
    @0
    @2
    restcldr
    mp2an
    @0
    @2
    cc
    cc
    @2
    @2
    @7
    cnfldtopon
    toponunii
    cldopn
    ax-mp
    eqeltri
end
