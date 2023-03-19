include "wcel.mm"
include "cpl1.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "wne.mm"
include "cco1.mm"
include "wceq.mm"
include "eqid.mm"
include "ismon1p.mm"
include "simp3bi.mm"

theorem mon1pldg
  let cD: class D
  let cR: class R
  let c.1: class .1.
  let cF: class F
  let cM: class M
  assume mon1pldg.d: |- D = ( deg1 ` R )
  assume mon1pldg.o: |- .1. = ( 1r ` R )
  assume mon1pldg.m: |- M = ( Monic1p ` R )


  assert |- ( F e. M -> ( ( coe1 ` F ) ` ( D ` F ) ) = .1. )

  proof
    cF
    cM
    wcel
    cF
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wcel
    cF
    @0
    c0g
    cfv
    #
    wne
    cF
    cD
    cfv
    cF
    cco1
    cfv
    cfv
    c.1
    wceq
    @1
    cD
    @0
    cR
    c.1
    cF
    cM
    @2
    @0
    eqid
    @1
    eqid
    @2
    eqid
    mon1pldg.d
    mon1pldg.m
    mon1pldg.o
    ismon1p
    simp3bi
end
