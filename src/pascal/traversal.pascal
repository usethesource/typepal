program traversal(input,output);

type ptr = ^node;
     node = record info: char;
               llink, rlink : ptr
            end;
var root : ptr; ch : char;

procedure preorder(p : ptr);
begin if p <> nil then
      begin write(p^.info);
        preorder(p^.llink);
        preorder(p^.rlink);
      end
end; {preorder}

begin
    preorder(root)
end.