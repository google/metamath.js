include "cnv.mm"
include "wcel.mm"
include "cc0.mm"
include "cns.mm"
include "cfv.mm"
include "co.mm"
include "cmul.mm"
include "cba.mm"
include "wceq.mm"
include "eqid.mm"
include "nvzcl.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "0re.mm"
include "0le0.mm"
include "pm3.2i.mm"
include "nvsge0.mm"
include "mp3an2.mm"
include "mpdan.mm"
include "nv0.mm"
include "fveq2d.mm"
include "cc.mm"
include "nvcl.mm"
include "recnd.mm"
include "mul02d.mm"
include "3eqtr3d.mm"

theorem nvz0
  let cU: class U
  let cN: class N
  let cZ: class Z
  assume nvz0.5: |- Z = ( 0vec ` U )
  assume nvz0.6: |- N = ( normCV ` U )


  assert |- ( U e. NrmCVec -> ( N ` Z ) = 0 )

  proof
    cU
    cnv
    wcel
    #
    cc0
    cZ
    cU
    cns
    cfv
    #
    co
    #
    cN
    cfv
    #
    cc0
    cZ
    cN
    cfv
    #
    cmul
    co
    #
    @4
    cc0
    @0
    cZ
    cU
    cba
    cfv
    #
    wcel
    #
    @3
    @5
    wceq
    #
    cU
    @6
    cZ
    @6
    eqid
    #
    nvz0.5
    nvzcl
    #
    @0
    cc0
    cr
    wcel
    #
    cc0
    cc0
    cle
    wbr
    #
    wa
    @7
    @8
    @11
    @12
    0re
    0le0
    pm3.2i
    cc0
    cZ
    @1
    cU
    cN
    @6
    @9
    @1
    eqid
    #
    nvz0.6
    nvsge0
    mp3an2
    mpdan
    @0
    @2
    cZ
    cN
    @0
    @7
    @2
    cZ
    wceq
    @10
    cZ
    @1
    cU
    @6
    cZ
    @9
    @13
    nvz0.5
    nv0
    mpdan
    fveq2d
    @0
    @4
    @0
    @7
    @4
    cc
    wcel
    @10
    @0
    @7
    wa
    @4
    cZ
    cU
    cN
    @6
    @9
    nvz0.6
    nvcl
    recnd
    mpdan
    mul02d
    3eqtr3d
end
