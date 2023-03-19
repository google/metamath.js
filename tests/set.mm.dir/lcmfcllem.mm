include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "cc0.mm"
include "wnel.mm"
include "w3a.mm"
include "clcmf.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "lcmfn0val.mm"
include "c1.mm"
include "cuz.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "fissn0dvdsn0.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem lcmfcllem
  let vm: setvar m
  let vn: setvar n
  let cZ: class Z
  let vz: setvar z

  disjoint Z m
  disjoint Z n
  disjoint m n
  disjoint Z z
  disjoint m z
  disjoint n z
  assert |- ( ( Z C_ ZZ /\ Z e. Fin /\ 0 e/ Z ) -> ( _lcm ` Z ) e. { n e. NN | A. m e. Z m || n } )

  proof
    cZ
    cz
    wss
    cZ
    cfn
    wcel
    cc0
    cZ
    wnel
    w3a
    #
    cZ
    clcmf
    cfv
    vm
    cv
    vn
    cv
    cdvds
    wbr
    vm
    cZ
    wral
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    @2
    vm
    vn
    cZ
    lcmfn0val
    @0
    @2
    c1
    cuz
    cfv
    #
    wss
    @2
    c0
    wne
    @3
    @2
    wcel
    @2
    cn
    @4
    @1
    vn
    cn
    ssrab2
    nnuz
    sseqtri
    vm
    vn
    cZ
    fissn0dvdsn0
    @2
    c1
    infssuzcl
    sylancr
    eqeltrd
end
