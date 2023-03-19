include "cmsr.mm"
include "cfv.mm"
include "ccnv.mm"
include "cmpps.mm"
include "cima.mm"
include "eqid.mm"
include "mthmval.mm"
include "cdm.mm"
include "cnvimass.mm"
include "msrf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "eqsstri.mm"

theorem mthmsta
  let cS: class S
  let cT: class T
  let cU: class U
  assume mthmsta.u: |- U = ( mThm ` T )
  assume mthmsta.s: |- S = ( mPreSt ` T )


  assert |- U C_ S

  proof
    cU
    cT
    cmsr
    cfv
    #
    ccnv
    @0
    cT
    cmpps
    cfv
    #
    cima
    #
    cima
    #
    cS
    @0
    cT
    cU
    @1
    @0
    eqid
    #
    @1
    eqid
    mthmsta.u
    mthmval
    @3
    @0
    cdm
    cS
    @0
    @2
    cnvimass
    cS
    cS
    @0
    cS
    @0
    cT
    mthmsta.s
    @4
    msrf
    fdmi
    sseqtri
    eqsstri
end
