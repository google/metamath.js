include "cv.mm"
include "wcel.mm"
include "com.mm"
include "word.mm"
include "cep.mm"
include "wfr.mm"
include "bnj923.mm"
include "nnord.mm"
include "ordfr.mm"
include "3syl.mm"

theorem bnj1071
  let cD: class D
  let vn: setvar n
  assume bnj1071.7: |- D = ( _om \ { (/) } )


  assert |- ( n e. D -> _E Fr n )

  proof
    vn
    cv
    #
    cD
    wcel
    @0
    com
    wcel
    @0
    word
    @0
    cep
    wfr
    cD
    vn
    bnj1071.7
    bnj923
    @0
    nnord
    @0
    ordfr
    3syl
end
