include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "csn.mm"
include "c0g.mm"
include "cfv.mm"
include "csubg.mm"
include "symgid.mm"
include "sneqd.mm"
include "cgrp.mm"
include "symggrp.mm"
include "eqid.mm"
include "0subg.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem idressubgsymg
  let cA: class A
  let cG: class G
  let cV: class V
  assume idresperm.g: |- G = ( SymGrp ` A )


  assert |- ( A e. V -> { ( _I |` A ) } e. ( SubGrp ` G ) )

  proof
    cA
    cV
    wcel
    #
    cid
    cA
    cres
    #
    csn
    cG
    c0g
    cfv
    #
    csn
    #
    cG
    csubg
    cfv
    #
    @0
    @1
    @2
    cA
    cG
    cV
    idresperm.g
    symgid
    sneqd
    @0
    cG
    cgrp
    wcel
    @3
    @4
    wcel
    cA
    cG
    cV
    idresperm.g
    symggrp
    cG
    @2
    @2
    eqid
    0subg
    syl
    eqeltrd
end
