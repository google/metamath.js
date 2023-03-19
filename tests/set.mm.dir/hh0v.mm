include "cn0v.mm"
include "cfv.mm"
include "cpv.mm"
include "cgi.mm"
include "cva.mm"
include "c0v.mm"
include "cnv.mm"
include "wcel.mm"
include "wceq.mm"
include "hhnv.mm"
include "eqid.mm"
include "0vfval.mm"
include "ax-mp.mm"
include "hhva.mm"
include "fveq2i.mm"
include "hilid.mm"
include "3eqtr2ri.mm"

theorem hh0v
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.


  assert |- 0h = ( 0vec ` U )

  proof
    cU
    cn0v
    cfv
    #
    cU
    cpv
    cfv
    #
    cgi
    cfv
    #
    cva
    cgi
    cfv
    c0v
    cU
    cnv
    wcel
    @0
    @2
    wceq
    cU
    hhnv.1
    hhnv
    cU
    @1
    cnv
    @0
    @1
    eqid
    @0
    eqid
    0vfval
    ax-mp
    cva
    @1
    cgi
    cU
    hhnv.1
    hhva
    fveq2i
    hilid
    3eqtr2ri
end
