include "cn.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "cc0.mm"
include "wnel.mm"
include "clcmf.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "id.mm"
include "nnssz.mm"
include "syl6ss.mm"
include "adantr.mm"
include "simpr.mm"
include "0nnn.mm"
include "nelir.mm"
include "ssel.mm"
include "nelcon3d.mm"
include "mpi.mm"
include "lcmfn0val.mm"
include "syl3anc.mm"

theorem lcmfnnval
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
  assert |- ( ( Z C_ NN /\ Z e. Fin ) -> ( _lcm ` Z ) = inf ( { n e. NN | A. m e. Z m || n } , RR , < ) )

  proof
    cZ
    cn
    wss
    #
    cZ
    cfn
    wcel
    #
    wa
    cZ
    cz
    wss
    #
    @1
    cc0
    cZ
    wnel
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
    vn
    cn
    crab
    cr
    clt
    cinf
    wceq
    @0
    @2
    @1
    @0
    cZ
    cn
    cz
    @0
    id
    nnssz
    syl6ss
    adantr
    @0
    @1
    simpr
    @0
    @3
    @1
    @0
    cc0
    cn
    wnel
    @3
    cc0
    cn
    0nnn
    nelir
    @0
    cc0
    cZ
    cc0
    cn
    cZ
    cn
    cc0
    ssel
    nelcon3d
    mpi
    adantr
    vm
    vn
    cZ
    lcmfn0val
    syl3anc
end
