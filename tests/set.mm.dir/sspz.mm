include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cnsb.mm"
include "cfv.mm"
include "co.mm"
include "cba.mm"
include "wceq.mm"
include "sspnv.mm"
include "eqid.mm"
include "nvzcl.mm"
include "jca.mm"
include "syl.mm"
include "sspmval.mm"
include "mpdan.mm"
include "nvmid.mm"
include "syl2anc.mm"
include "sspba.mm"
include "sseldd.mm"
include "syldan.mm"
include "3eqtr3d.mm"

theorem sspz
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cW: class W
  let cZ: class Z
  assume sspz.z: |- Z = ( 0vec ` U )
  assume sspz.q: |- Q = ( 0vec ` W )
  assume sspz.h: |- H = ( SubSp ` U )


  assert |- ( ( U e. NrmCVec /\ W e. H ) -> Q = Z )

  proof
    cU
    cnv
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cQ
    cQ
    cW
    cnsb
    cfv
    #
    co
    #
    cQ
    cQ
    cU
    cnsb
    cfv
    #
    co
    #
    cQ
    cZ
    @2
    cQ
    cW
    cba
    cfv
    #
    wcel
    #
    @8
    wa
    #
    @4
    @6
    wceq
    @2
    cW
    cnv
    wcel
    #
    @9
    cU
    cH
    cW
    sspz.h
    sspnv
    #
    @10
    @8
    @8
    cW
    @7
    cQ
    @7
    eqid
    #
    sspz.q
    nvzcl
    #
    @13
    jca
    syl
    cQ
    cQ
    cU
    cH
    @3
    @5
    cW
    @7
    @12
    @5
    eqid
    #
    @3
    eqid
    #
    sspz.h
    sspmval
    mpdan
    @2
    @10
    @8
    @4
    cQ
    wceq
    @11
    @2
    @10
    @8
    @11
    @13
    syl
    #
    cQ
    cW
    @3
    @7
    cQ
    @12
    @15
    sspz.q
    nvmid
    syl2anc
    @0
    @1
    cQ
    cU
    cba
    cfv
    #
    wcel
    @6
    cZ
    wceq
    @2
    @7
    @17
    cQ
    cU
    cH
    cW
    @17
    @7
    @17
    eqid
    #
    @12
    sspz.h
    sspba
    @16
    sseldd
    cQ
    cU
    @5
    @17
    cZ
    @18
    @14
    sspz.z
    nvmid
    syldan
    3eqtr3d
end
