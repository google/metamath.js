include "cfield.mm"
include "wcel.mm"
include "ccrg.mm"
include "cdomn.mm"
include "cidom.mm"
include "cdr.mm"
include "isfld.mm"
include "simprbi.mm"
include "simplbi.mm"
include "drngdomn.mm"
include "syl.mm"
include "isidom.mm"
include "sylanbrc.mm"

theorem fldidom
  let cR: class R


  assert |- ( R e. Field -> R e. IDomn )

  proof
    cR
    cfield
    wcel
    #
    cR
    ccrg
    wcel
    #
    cR
    cdomn
    wcel
    #
    cR
    cidom
    wcel
    @0
    cR
    cdr
    wcel
    #
    @1
    cR
    isfld
    #
    simprbi
    @0
    @3
    @2
    @0
    @3
    @1
    @4
    simplbi
    cR
    drngdomn
    syl
    cR
    isidom
    sylanbrc
end
