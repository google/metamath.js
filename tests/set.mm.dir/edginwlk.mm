include "wfun.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "crn.mm"
include "simp1.mm"
include "wrdsymbcl.mm"
include "3adant1.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "cedg.mm"
include "ciedg.mm"
include "edgval.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "3eqtri.mm"
include "syl6eleqr.mm"

theorem edginwlk
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  assume edginwlk.i: |- I = ( iEdg ` G )
  assume edginwlk.e: |- E = ( Edg ` G )


  assert |- ( ( Fun I /\ F e. Word dom I /\ K e. ( 0 ..^ ( # ` F ) ) ) -> ( I ` ( F ` K ) ) e. E )

  proof
    cI
    wfun
    #
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    cK
    cc0
    cF
    chash
    cfv
    cfzo
    co
    wcel
    #
    w3a
    #
    cK
    cF
    cfv
    #
    cI
    cfv
    #
    cI
    crn
    #
    cE
    @4
    @0
    @5
    @1
    wcel
    #
    @6
    @7
    wcel
    @0
    @2
    @3
    simp1
    @2
    @3
    @8
    @0
    cK
    @1
    cF
    wrdsymbcl
    3adant1
    @5
    cI
    fvelrn
    syl2anc
    cE
    cG
    cedg
    cfv
    cG
    ciedg
    cfv
    #
    crn
    @7
    edginwlk.e
    cG
    edgval
    @9
    cI
    cI
    @9
    edginwlk.i
    eqcomi
    rneqi
    3eqtri
    syl6eleqr
end
