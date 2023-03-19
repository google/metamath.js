include "chil.mm"
include "wcel.mm"
include "cc0.mm"
include "cpjh.mm"
include "cfv.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csp.mm"
include "cle.mm"
include "cr.mm"
include "pjhcli.mm"
include "normcl.mm"
include "syl.mm"
include "sqge0d.mm"
include "pjinormi.mm"
include "breqtrrd.mm"

theorem pjige0i
  let cA: class A
  let cH: class H
  assume pjadjt.1: |- H e. CH


  assert |- ( A e. ~H -> 0 <_ ( ( ( projh ` H ) ` A ) .ih A ) )

  proof
    cA
    chil
    wcel
    #
    cc0
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    @1
    cA
    csp
    co
    cle
    @0
    @2
    @0
    @1
    chil
    wcel
    @2
    cr
    wcel
    cA
    cH
    pjadjt.1
    pjhcli
    @1
    normcl
    syl
    sqge0d
    cA
    cH
    pjadjt.1
    pjinormi
    breqtrrd
end
