include "cn.mm"
include "cv.mm"
include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "c7.mm"
include "cpr.mm"
include "cneg.mm"
include "cif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "cpc.mm"
include "cmpt.mm"
include "eqid.mm"
include "lgscllem.mm"

theorem lgscl2
  let vx: setvar x
  let cA: class A
  let cN: class N
  let cZ: class Z
  let vn: setvar n
  assume lgscl2.z: |- Z = { x e. ZZ | ( abs ` x ) <_ 1 }

  disjoint A x
  disjoint N x
  disjoint n x
  disjoint A n
  disjoint N n
  disjoint Z n
  assert |- ( ( A e. ZZ /\ N e. ZZ ) -> ( A /L N ) e. Z )

  proof
    vx
    cA
    vn
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    @0
    c2
    wceq
    c2
    cA
    cdvds
    wbr
    cc0
    cA
    c8
    cmo
    co
    c1
    c7
    cpr
    wcel
    c1
    c1
    cneg
    cif
    cif
    cA
    @0
    c1
    cmin
    co
    c2
    cdiv
    co
    cexp
    co
    c1
    caddc
    co
    @0
    cmo
    co
    c1
    cmin
    co
    cif
    @0
    cN
    cpc
    co
    cexp
    co
    c1
    cif
    cmpt
    #
    cN
    cZ
    @1
    eqid
    lgscl2.z
    lgscllem
end
