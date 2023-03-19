include "cv.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "ciun.mm"
include "cdif.mm"
include "cmpt.mm"
include "eqid.mm"
include "meaiunlelem.mm"

theorem meaiunle
  let wph: wff ph
  let cS: class S
  let vn: setvar n
  let cE: class E
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume meaiunle.nph: |- F/ n ph
  assume meaiunle.m: |- ( ph -> M e. Meas )
  assume meaiunle.s: |- S = dom M
  assume meaiunle.z: |- Z = ( ZZ>= ` N )
  assume meaiunle.e: |- ( ph -> E : Z --> S )

  disjoint E n
  disjoint M n
  disjoint N n
  disjoint S n
  disjoint Z n
  disjoint E x
  disjoint n x
  disjoint N x
  disjoint S x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( M ` U_ n e. Z ( E ` n ) ) <_ ( sum^ ` ( n e. Z |-> ( M ` ( E ` n ) ) ) ) )

  proof
    wph
    cS
    vx
    vn
    cE
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    vx
    cN
    @0
    cfzo
    co
    vx
    cv
    cE
    cfv
    ciun
    cdif
    cmpt
    #
    cM
    cN
    cZ
    meaiunle.nph
    meaiunle.m
    meaiunle.s
    meaiunle.z
    meaiunle.e
    @1
    eqid
    meaiunlelem
end
