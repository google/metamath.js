include "cst.mm"
include "wcel.mm"
include "c1.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cort.mm"
include "wceq.mm"
include "caddc.mm"
include "sto1i.mm"
include "cc.mm"
include "wb.mm"
include "cch.mm"
include "cr.mm"
include "stcl.mm"
include "mpi.mm"
include "recnd.mm"
include "choccli.mm"
include "ax-1cn.mm"
include "subadd.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem sto2i
  let cA: class A
  let cS: class S
  assume sto1.1: |- A e. CH


  assert |- ( S e. States -> ( S ` ( _|_ ` A ) ) = ( 1 - ( S ` A ) ) )

  proof
    cS
    cst
    wcel
    #
    c1
    cA
    cS
    cfv
    #
    cmin
    co
    #
    cA
    cort
    cfv
    #
    cS
    cfv
    #
    @0
    @2
    @4
    wceq
    #
    @1
    @4
    caddc
    co
    c1
    wceq
    #
    cA
    cS
    sto1.1
    sto1i
    @0
    @1
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @5
    @6
    wb
    #
    @0
    @1
    @0
    cA
    cch
    wcel
    @1
    cr
    wcel
    sto1.1
    cA
    cS
    stcl
    mpi
    recnd
    @0
    @4
    @0
    @3
    cch
    wcel
    @4
    cr
    wcel
    cA
    sto1.1
    choccli
    @3
    cS
    stcl
    mpi
    recnd
    c1
    cc
    wcel
    @7
    @8
    @9
    ax-1cn
    c1
    @1
    @4
    subadd
    mp3an1
    syl2anc
    mpbird
    eqcomd
end
