include "caddc.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cvol.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "eqid.mm"
include "voliunsge0lem.mm"

theorem voliunsge0
  let wph: wff ph
  let vn: setvar n
  let cE: class E
  let vk: setvar k
  let vx: setvar x
  assume voliunsge0.1: |- ( ph -> E : NN --> dom vol )
  assume voliunsge0.2: |- ( ph -> Disj_ n e. NN ( E ` n ) )

  disjoint E n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( vol ` U_ n e. NN ( E ` n ) ) = ( sum^ ` ( n e. NN |-> ( vol ` ( E ` n ) ) ) ) )

  proof
    wph
    caddc
    vn
    cn
    vn
    cv
    cE
    cfv
    cvol
    cfv
    cmpt
    #
    c1
    cseq
    #
    vn
    cE
    @0
    @1
    eqid
    @0
    eqid
    voliunsge0.1
    voliunsge0.2
    voliunsge0lem
end
