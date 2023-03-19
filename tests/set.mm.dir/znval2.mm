include "cn0.mm"
include "wcel.mm"
include "cnx.mm"
include "cple.mm"
include "cfv.mm"
include "czrh.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "cfzo.mm"
include "co.mm"
include "cif.mm"
include "cres.mm"
include "cle.mm"
include "ccom.mm"
include "ccnv.mm"
include "cop.mm"
include "csts.mm"
include "eqid.mm"
include "znval.mm"
include "znle.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem znval2
  let cS: class S
  let cU: class U
  let c.le: class .<_
  let cN: class N
  let cY: class Y
  let cE: class E
  let vx: setvar x
  let cK: class K
  let vy: setvar y
  assume znval2.s: |- S = ( RSpan ` ZZring )
  assume znval2.u: |- U = ( ZZring /s ( ZZring ~QG ( S ` { N } ) ) )
  assume znval2.y: |- Y = ( Z/nZ ` N )
  assume znval2.l: |- .<_ = ( le ` Y )


  assert |- ( N e. NN0 -> Y = ( U sSet <. ( le ` ndx ) , .<_ >. ) )

  proof
    cN
    cn0
    wcel
    #
    cY
    cU
    cnx
    cple
    cfv
    #
    cU
    czrh
    cfv
    cN
    cc0
    wceq
    cz
    cc0
    cN
    cfzo
    co
    cif
    #
    cres
    #
    cle
    ccom
    @3
    ccnv
    ccom
    #
    cop
    #
    csts
    co
    cU
    @1
    c.le
    cop
    #
    csts
    co
    cS
    cU
    @3
    @4
    cN
    @2
    cY
    znval2.s
    znval2.u
    znval2.y
    @3
    eqid
    #
    @2
    eqid
    #
    @4
    eqid
    znval
    @0
    @6
    @5
    cU
    csts
    @0
    c.le
    @4
    @1
    cS
    cU
    @3
    c.le
    cN
    @2
    cY
    znval2.s
    znval2.u
    znval2.y
    @7
    @8
    znval2.l
    znle
    opeq2d
    oveq2d
    eqtr4d
end
