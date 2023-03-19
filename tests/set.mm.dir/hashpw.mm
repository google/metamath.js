include "cv.mm"
include "cpw.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cfn.mm"
include "pweq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "wcel.mm"
include "c2o.mm"
include "cmap.mm"
include "cen.mm"
include "wbr.mm"
include "vex.mm"
include "pw2en.mm"
include "wb.mm"
include "pwfi.mm"
include "biimpi.mm"
include "c0.mm"
include "csn.mm"
include "cpr.mm"
include "df2o2.mm"
include "prfi.mm"
include "eqeltri.mm"
include "mapfi.mm"
include "mpan.mm"
include "hashen.mm"
include "syl2anc.mm"
include "mpbiri.mm"
include "hashmap.mm"
include "hash2.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "vtoclga.mm"

theorem hashpw
  let cA: class A
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( A e. Fin -> ( # ` ~P A ) = ( 2 ^ ( # ` A ) ) )

  proof
    vx
    cv
    #
    cpw
    #
    chash
    cfv
    #
    c2
    @0
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    cA
    cpw
    #
    chash
    cfv
    #
    c2
    cA
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    vx
    cA
    cfn
    @0
    cA
    wceq
    #
    @2
    @6
    @4
    @8
    @9
    @1
    @5
    chash
    @0
    cA
    pweq
    fveq2d
    @9
    @3
    @7
    c2
    cexp
    @0
    cA
    chash
    fveq2
    oveq2d
    eqeq12d
    @0
    cfn
    wcel
    #
    @2
    c2o
    @0
    cmap
    co
    #
    chash
    cfv
    #
    @4
    @10
    @2
    @12
    wceq
    #
    @1
    @11
    cen
    wbr
    #
    @0
    vx
    vex
    pw2en
    @10
    @1
    cfn
    wcel
    #
    @11
    cfn
    wcel
    #
    @13
    @14
    wb
    @10
    @15
    @0
    pwfi
    biimpi
    c2o
    cfn
    wcel
    #
    @10
    @16
    c2o
    c0
    c0
    csn
    #
    cpr
    cfn
    df2o2
    c0
    @18
    prfi
    eqeltri
    #
    c2o
    @0
    mapfi
    mpan
    @1
    @11
    hashen
    syl2anc
    mpbiri
    @10
    @12
    c2o
    chash
    cfv
    #
    @3
    cexp
    co
    #
    @4
    @17
    @10
    @12
    @21
    wceq
    @19
    c2o
    @0
    hashmap
    mpan
    @20
    c2
    @3
    cexp
    hash2
    oveq1i
    syl6eq
    eqtrd
    vtoclga
end
